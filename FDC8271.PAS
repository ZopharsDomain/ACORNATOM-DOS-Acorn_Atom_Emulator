(***************************************************************************)
(*                                                                         *)
(* Floppy Disk Controller 8271 for the Acorn Atom Emulator v1.31 (c) W.Ras *)
(* ----------------------------------------------------------------------- *)
(*                                                                         *)
(* This source code may be distributed freely within the following         *)
(* restrictions                                                            *)
(* 1. You may not charge for this program or for any part of it.           *)
(* 2. This copyright message may not be removed from it.                   *)
(* 3. You may use sections of code from this program in your applications, *)
(*    but you must acknowledge its use. I'd appreciate it if you'd let me  *)
(*    know, i.e. send me a copy of your work.                              *)
(*                                                                         *)
(* Please report any problems, questions, comments to me at this address:  *)
(* avio@casema.net                                                         *)
(*                                                                         *)
(* The latest version of the emulator can be downloaded from my Atom-page: *)
(* http://www.casema.net/~avio/atom.htm                                    *)
(*                                                                         *)
(***************************************************************************)

{$g+,f+,i-,r-,s-}
UNIT FDC8271;


INTERFACE

VAR DUMMY:BYTE; {!!!must not be separated from WRITEPROTECT!!!}
    WRITEPROTECT:ARRAY[0..1] OF BYTE; {write protect drive 0/2 and 1/3; xF/Fx=protected}
    DISKETTENAMES:ARRAY[0..3] OF STRING[13];

PROCEDURE CLRDRIVETXT;
PROCEDURE READ_FDC;
PROCEDURE WRITE_FDC;
PROCEDURE FDC_NMI_HANDLER;
PROCEDURE OPEN_DISK_IMAGE (DRIVENR:BYTE; NOWRITE:BOOLEAN);
PROCEDURE CLOSE_DISK_IMAGE (DRIVENR:BYTE);


IMPLEMENTATION

CONST NMI = $BFF6; {---same address as IRQ in main program---}
VAR IMAGENAAM:ARRAY[0..12] OF CHAR;

{$f-}
PROCEDURE CMDDEST; ASSEMBLER;
ASM;
               DW    $0000
END;

PROCEDURE DRVCTRLOUTP; ASSEMBLER;
ASM;
               DB    $00
END;

PROCEDURE SETDRIVETXT; ASSEMBLER;
ASM;
               PUSH  DI
               PUSH  BX
               PUSH  CX
               MOV   DI,$DCA0
               MOV   CH,+8
@SETDR2:       MOV   CL,+6
@SETDR1:       MOV   WORD PTR [ES:DI],$FFFF
               MOV   WORD PTR [ES:DI+$02],$FF00
               MOV   WORD PTR [ES:DI+32],$FFFF
               MOV   WORD PTR [ES:DI+32+$02],$FF00
               ADD   DI,+$04
               DEC   CL
               JNZ   @SETDR1
               ADD   DI,$0120-6*$04
               DEC   CH
               CMP   CH,+4
               JNZ   @SETDR5
               ADD   DI,$0120
@SETDR5:       OR    CH,CH
               JNZ   @SETDR2
               MOV   DI,$E120
               MOV   CH,+2
@SETDR4:       MOV   WORD PTR [ES:DI],$F0FF
               MOV   WORD PTR [ES:DI+$02],$FF0F
               ADD   DI,+$04
               MOV   CL,+4
@SETDR3:       MOV   WORD PTR [ES:DI],$00FF
               MOV   WORD PTR [ES:DI+$02],$FFFF
               ADD   DI,+$04
               DEC   CL
               JNZ   @SETDR3
               MOV   WORD PTR [ES:DI],$0FFF
               MOV   WORD PTR [ES:DI+$02],$FFF0
               ADD   DI,+$0C
               DEC   CH
               JNZ   @SETDR4
              {SUB   CX,CX}
               MOV   WORD PTR @LIGHTCOLOR[$00],CX
               MOV   WORD PTR @LIGHTCOLOR[$02],CX
               MOV   BL,BYTE PTR [CS:CMDDEST+$01]
               AND   BL,$01
               TEST  BYTE PTR [CS:DRVCTRLOUTP],00100000b
               JZ    @SETDR6
               OR    BL,$02
@SETDR6:       MOV   BH,$00
               MOV   BYTE PTR @LIGHTCOLOR[BX],$01
               MOV   BX,+3
@SETDR9:       SHL   BX,1
               MOV   DI,WORD PTR @LIGHTPOS[BX]
               SHR   BX,1
               CMP   BYTE PTR @LIGHTCOLOR[BX],$00
               JNZ   @SETDR7
               MOV   WORD PTR [ES:DI],$F0FF
               MOV   WORD PTR [ES:DI+$02],$FF0F
               MOV   WORD PTR [ES:DI+$04],$0FFF
               MOV   WORD PTR [ES:DI+$06],$FFF0
               JMP   @SETDR8
@SETDR7:       MOV   WORD PTR [ES:DI],$F0FF
               MOV   WORD PTR [ES:DI+$02],$FF00
               MOV   WORD PTR [ES:DI+$04],$0FFF
               MOV   WORD PTR [ES:DI+$06],$FF00
@SETDR8:       DEC   BX
               JNS   @SETDR9
               POP   CX
               POP   BX
               POP   DI
               RET
@LIGHTCOLOR:   DB    $00,$00,$00,$00
@LIGHTPOS:     DW    $DEE8,$DF08,$E368,$E388
END;

{---[clrdrivetxt]-----------------------------------------------------------}
PROCEDURE CLRDRIVETXT; ASSEMBLER;
ASM;
               PUSH  DI
               PUSH  CX
               MOV   DI,$DCA0
               MOV   CH,+9
@CLRDR2:       MOV   CL,+6
@CLRDR1:       MOV   WORD PTR [ES:DI],$FFFF
               MOV   WORD PTR [ES:DI+$02],$00FF
               MOV   WORD PTR [ES:DI+32],$FFFF
               MOV   WORD PTR [ES:DI+32+$02],$00FF
               ADD   DI,+$04
               DEC   CL
               JNZ   @CLRDR1
               ADD   DI,$0120-6*$04
               DEC   CH
               JNZ   @CLRDR2
               POP   CX
               POP   DI
END;

PROCEDURE FILEHANDLES; ASSEMBLER;
ASM;
               DW    $0000
               DW    $0000
               DW    $0000
               DW    $0000
END;

PROCEDURE CALL_FDC; ASSEMBLER;
ASM;
               AND   DI,$00FF
               SHL   DI,1
               CMP   AH,$01
               JA    @CALL_FDC2
               JZ    @CALL_FDC1
               {---read reg---}
               CMP   DI,+4*2
               JA    @CALL_FDC3
               JMP   WORD PTR @READTABLE[DI]
@CALL_FDC1:    {---write reg---}
               CMP   DI,+4*2
               JA    @CALL_FDC4
               JMP   WORD PTR @WRITETABLE[DI]
@CALL_FDC2:    {---nmi handler---}
               JMP   WORD PTR @NMIHNDLR
@CALL_FDC3:    MOV   AL,$00
@CALL_FDC4:    RETN

@READTABLE:    DW    OFFSET @READFDC00
               DW    OFFSET @READFDC01
               DW    OFFSET @READFDC02
               DW    OFFSET @READFDC03
               DW    OFFSET @READFDC04

@WRITETABLE:   DW    OFFSET @WRITEFDC00
               DW    OFFSET @WRITEFDC01
               DW    OFFSET @WRITEFDC02
               DW    OFFSET @WRITEFDC03
               DW    OFFSET @WRITEFDC04

@COMMANDTABLE: DB    $00,$3F,$03; DW OFFSET @COMMAND00
               DB    $04,$3F,$03; DW OFFSET @COMMAND04
               DB    $0A,$3F,$02; DW OFFSET @COMMAND0A
               DB    $0B,$3F,$03; DW OFFSET @COMMAND0B
               DB    $0E,$3F,$02; DW OFFSET @COMMAND0E
               DB    $0F,$3F,$03; DW OFFSET @COMMAND0F
               DB    $12,$3F,$02; DW OFFSET @COMMAND12
               DB    $13,$3F,$03; DW OFFSET @COMMAND13
               DB    $16,$3F,$02; DW OFFSET @COMMAND16
               DB    $17,$3F,$03; DW OFFSET @COMMAND17
               DB    $1B,$3F,$03; DW OFFSET @COMMAND1B
               DB    $1E,$3F,$02; DW OFFSET @COMMAND1E
               DB    $1F,$3F,$03; DW OFFSET @COMMAND1F
               DB    $23,$3F,$05; DW OFFSET @COMMAND23
               DB    $29,$3F,$01; DW OFFSET @COMMAND29
               DB    $2C,$3F,$00; DW OFFSET @COMMAND2C
               DB    $35,$FF,$04; DW OFFSET @COMMAND35
               DB    $3A,$3F,$02; DW OFFSET @COMMAND3A
               DB    $3D,$3F,$01; DW OFFSET @COMMAND3D
               DB    $00,$00,$00; DW OFFSET @NOCOMMAND

@STATUSREG:    DB    $00
@RESULTREG:    DB    $00
@COMMANDREG:   DB    $00
@PARAMREG:     DB    $00
@RESETREG:     DB    $00
@DATAREG:      DB    $00

@ERRORNR:      DB    $00
@MODEREG:      DB    $00   {!!!do not separate @modereg and @headpos!!!}
@HEADPOS:      DW    $0000 {head position for drive 0/2 and 1/3}
@FDCREG06:     DB    $00
@FDCREG10:     DB    $00
@FDCREG11:     DB    $00
@FDCREG13:     DB    $00
@FDCREG18:     DB    $00
@FDCREG19:     DB    $00
@FDCREG22:     DB    $00

@AANTALPARAM:  DB    $00
@COMMANDHNDLR: DW    $0000
@PARAMTELLER:  DB    $00
@PARAMETERS:   DD    $00000000,$00000000

@NMIHNDLR:     DW    OFFSET @NONMI
@TRACK:        DB    $00
@SECTOR:       DB    $00
@AANTALSECT:   DB    $00
@BYTESPERSECT: DW    $0000
@BUFPTR:       DW    $0000
@BUFFER:       DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
               DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
               DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
               DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0

{---[saveerrornr]-----------------------------------------------------------}
@SAVEERRORNR:  MOV   BYTE PTR @ERRORNR,AL
               MOV   BYTE PTR @STATUSREG,10000000b
               OR    BYTE PTR [NMI],$80
               RETN

{---[setcmddest]------------------------------------------------------------}
@SETCMDDEST:   PUSH  AX
               SUB   AX,AX
               TEST  BYTE PTR @COMMANDREG,01000000b
               JZ    @SETCMDDEST1
               DEC   AL
@SETCMDDEST1:  TEST  BYTE PTR @COMMANDREG,10000000b
               JZ    @SETCMDDEST2
               DEC   AH
@SETCMDDEST2:  MOV   WORD PTR [CS:CMDDEST],AX
               POP   AX
               RETN

{---[getDIfordrive]---------------------------------------------------------}
@GETDIFORDRIVE:MOV   DI,-1  {--> points to @modereg}
               CMP   WORD PTR [CS:CMDDEST],$0000
               JZ    @GETDI1
               INC   DI     {--> points to @headpos 0/2}
               CMP   BYTE PTR [CS:CMDDEST+$01],$00
               JZ    @GETDI1
               INC   DI     {--> points to @headpos 1/3}
@GETDI1:       RETN

{---[chkdriveready (carry clear if successful)]-----------------------------}
@CHKDRIVEREADY:CMP   WORD PTR [CS:CMDDEST],$0000
               CLC
               JNZ   @CHKDRVREADY1
@DRVNOTREADY:  MOV   AL,$10
               CALL  @SAVEERRORNR
               STC
@CHKDRVREADY1: RETN

{---[chkwriteprot (carry clear if no writeprotect)]-------------------------}
@CHKWRITEPROT: PUSH  DS
               PUSH  AX
               MOV   AX,SEG WRITEPROTECT
               MOV   DS,AX
               MOV   AL,BYTE PTR WRITEPROTECT[DI]
               TEST  BYTE PTR [CS:DRVCTRLOUTP],00100000b
               JZ    @CHKWRITEPROT2
               SHR   AL,4
@CHKWRITEPROT2:AND   AL,$01
               POP   AX
               POP   DS
               CLC
               JZ    @CHKWRITEPROT1
               MOV   AL,$12
               CALL  @SAVEERRORNR
               STC
@CHKWRITEPROT1:RETN

{---[chklegalpos (carry clear if successful)]-------------------------------}
@CHKLEGALPOS:  CMP   BYTE PTR @TRACK,+40
               JAE   @CHKLEGAL1
               CMP   BYTE PTR @SECTOR,+10
               JAE   @CHKLEGAL1
               CMP   WORD PTR @BYTESPERSECT,$0100
               JNZ   @CHKLEGAL1
               CLC
               RETN
@CHKLEGAL1:    MOV   AL,$1E
               CALL  @SAVEERRORNR
               STC
               RETN

{---[checkerror (carry set on error)]---------------------------------------}
@CHECKERROR:   OR    BYTE PTR @STATUSREG,00001000b
               CMP   BYTE PTR @ERRORNR,$00
               JZ    @CHKERR1
               MOV   AL,$00
               XCHG  AL,BYTE PTR @ERRORNR
               MOV   BYTE PTR @RESULTREG,AL
               MOV   BYTE PTR @STATUSREG,00011000b
               MOV   WORD PTR @NMIHNDLR,OFFSET @NONMI
               CALL  CLRDRIVETXT
               STC
               RETN
@CHKERR1:      CLC
               RETN

{---[seekfilepos]-----------------------------------------------------------}
@SEEKFILEPOS:  MOV   AL,BYTE PTR @TRACK
               MOV   CL,+10
               MUL   CL
               MOV   CH,BYTE PTR @SECTOR
               CMP   CH,CL
               JAE   @SEEKF1
               ADD   AL,CH
               ADC   AH,$00
@SEEKF1:       SUB   CX,CX
               XCHG  AL,AH
               XCHG  CL,AL
               MOV   DX,AX {---CX:DX=filepos---}
               MOV   AX,$4200
               CALL  @GETFILEHANDLE
               JZ    @DRVNOTREADY
               INT   $21
               JC    @DRVNOTREADY
              {CLC}
               RETN

{---[getfilehandle]---------------------------------------------------------}
@GETFILEHANDLE:MOV   BL,BYTE PTR [CS:CMDDEST+$01]
               AND   BX,+$02
               TEST  BYTE PTR [CS:DRVCTRLOUTP],00100000b
               JZ    @GETFHNDL1
               OR    BL,$04
@GETFHNDL1:    MOV   BX,WORD PTR FILEHANDLES[CS:BX]
               OR    BX,BX
               RETN

{---[readfdc00: read status]------------------------------------------------}
@READFDC00:    MOV   AL,BYTE PTR @STATUSREG
               MOV   BYTE PTR [$BA00],AL {for debug purposes only}
               RETN

{---[readfdc01: read result]------------------------------------------------}
@READFDC01:    AND   BYTE PTR @STATUSREG,11100111b
               MOV   AL,$00
               XCHG  AL,BYTE PTR @RESULTREG
               MOV   BYTE PTR [$BA01],AL {for debug purposes only}
               RETN

{---[readfdc02/03]----------------------------------------------------------}
@READFDC02:
@READFDC03:    MOV   AL,$00
               RETN

{---[readfdc04: read data]--------------------------------------------------}
@READFDC04:    AND   BYTE PTR @STATUSREG,11110011b
               MOV   AL,BYTE PTR @DATAREG
               MOV   BYTE PTR [$BA04],AL {for debug purposes only}
               RETN

{---[writefdc00: write command]---------------------------------------------}
@WRITEFDC00:   PUSH  BX
               MOV   BX,-5
@WRFDC00_1:    ADD   BX,+5
               MOV   AH,AL
               AND   AH,BYTE PTR @COMMANDTABLE[BX+$01]
               CMP   AH,BYTE PTR @COMMANDTABLE[BX]
               JNZ   @WRFDC00_1
               MOV   BYTE PTR @COMMANDREG,AL
               MOV   AL,BYTE PTR @COMMANDTABLE[BX+$02]
               MOV   BYTE PTR @AANTALPARAM,AL
               MOV   AX,WORD PTR @COMMANDTABLE[BX+$03]
               MOV   WORD PTR @COMMANDHNDLR,AX
               POP   BX
               MOV   BYTE PTR @PARAMTELLER,$00
               OR    BYTE PTR @STATUSREG,10010000b
               CMP   BYTE PTR @AANTALPARAM,$00
               JNZ   @WRFDC00_2
               AND   BYTE PTR @STATUSREG,01111110b
               PUSHA
               CALL  WORD PTR @COMMANDHNDLR
               POPA
@WRFDC00_2:    RETN

{---[writefdc01: write parameter]-------------------------------------------}
@WRITEFDC01:   PUSH  BX
               MOV   BL,BYTE PTR @PARAMTELLER
               AND   BX,$0007
               CMP   BL,BYTE PTR @AANTALPARAM
               JAE   @WRFDC01_2
               MOV   BYTE PTR @PARAMETERS[BX],AL
               INC   BL
               MOV   BYTE PTR @PARAMTELLER,BL
               AND   BYTE PTR @STATUSREG,11111110b
               CMP   BL,BYTE PTR @AANTALPARAM
               JNZ   @WRFDC01_2
               AND   BYTE PTR @STATUSREG,01111110b
               PUSHA
               CALL  WORD PTR @COMMANDHNDLR
               POPA
@WRFDC01_2:    POP   BX
               RETN

{---[writefdc02: reset fdc]-------------------------------------------------}
@WRITEFDC02:   MOV   AL,$00
               MOV   BYTE PTR @STATUSREG,AL
               MOV   BYTE PTR @RESULTREG,AL
               MOV   BYTE PTR @FDCREG06,AL
               MOV   BYTE PTR @HEADPOS[$00],AL
               MOV   BYTE PTR @FDCREG13,AL
               MOV   BYTE PTR @HEADPOS[$01],AL
               MOV   BYTE PTR @FDCREG22,AL
               MOV   BYTE PTR [CS:DRVCTRLOUTP],AL
               MOV   BYTE PTR @AANTALPARAM,AL
               MOV   BYTE PTR @ERRORNR,AL
               DEC   AL
               MOV   BYTE PTR @COMMANDREG,AL
               MOV   BYTE PTR @FDCREG10,AL
               MOV   BYTE PTR @FDCREG11,AL
               MOV   BYTE PTR @FDCREG18,AL
               MOV   BYTE PTR @FDCREG19,AL
@WRITEFDC03:   RETN

{---[writefdc04: write data]------------------------------------------------}
@WRITEFDC04:   AND   BYTE PTR @STATUSREG,11110011b
               MOV   BYTE PTR @DATAREG,AL
               MOV   BYTE PTR [$BA04],AL {for debug purposes only}
               RETN

{---[fdc commands]----------------------------------------------------------}
@COMMAND00:
@COMMAND04:
@COMMAND0A:
@COMMAND0E:
@COMMAND0F:
@COMMAND12:
@COMMAND16:
@COMMAND17:
@COMMAND1E:
               CALL  @SETCMDDEST
@COMMAND35:
@NOCOMMAND:    RETN


{---[command0B: write data variable length/multi-record format]-------------}
@COMMAND0B:    MOV   WORD PTR @NMIHNDLR,OFFSET @WRITEDAT
               CALL  @SETCMDDEST
               CALL  @CHKDRIVEREADY
               JC    @CMD0B_1
               CALL  @GETDIFORDRIVE
               CALL  @CHKWRITEPROT
               JC    @CMD0B_1
               MOV   AL,BYTE PTR @PARAMETERS[$00]
               MOV   BYTE PTR @HEADPOS[DI],AL
               MOV   BYTE PTR @TRACK,AL
               MOV   AL,BYTE PTR @PARAMETERS[$01]
               MOV   BYTE PTR @SECTOR,AL
               MOV   AL,BYTE PTR @PARAMETERS[$02]
               MOV   CL,AL
               AND   AL,00011111b
               MOV   BYTE PTR @AANTALSECT,AL
               SHR   CL,5
               ADD   CL,$07
               MOV   AX,$0001
               SHL   AX,CL
               MOV   WORD PTR @BYTESPERSECT,AX
               CALL  @CHKLEGALPOS
               JC    @CMD0B_1
               CALL  @SEEKFILEPOS
               JC    @CMD0B_1
               MOV   WORD PTR @BUFPTR,-1
               OR    BYTE PTR [NMI],$80
               MOV   BYTE PTR @STATUSREG,10001100b
               CALL  SETDRIVETXT
@CMD0B_1:      RETN

@WRITEDAT:     CALL  @CHECKERROR
               JC    @WRITED6
               CMP   BYTE PTR @AANTALSECT,$00
               JZ    @WRITED1
               MOV   SI,WORD PTR @BUFPTR
               CMP   SI,$0100
               JAE   @WRITED2
               MOV   AL,BYTE PTR @DATAREG
               MOV   BYTE PTR @BUFFER[SI],AL
@WRITED2:      INC   SI
               MOV   WORD PTR @BUFPTR,SI
               MOV   BYTE PTR @RESULTREG,$00
               CMP   SI,WORD PTR @BYTESPERSECT
               JL    @WRITED3
               MOV   WORD PTR @BUFPTR,$0000
               MOV   AH,$40
               CALL  @GETFILEHANDLE
               JZ    @WRITED4
               MOV   CX,$0100
               MOV   DX,OFFSET @BUFFER
               PUSH  DS
               PUSH  CS
               POP   DS
               INT   $21 {---write data to disk image---}
               POP   DS
               JC    @WRITED4
               DEC   BYTE PTR @AANTALSECT
               JZ    @WRITED5
               INC   BYTE PTR @SECTOR
               CALL  @CHKLEGALPOS
               JNC   @WRITED3
@WRITED6:      RETN
@WRITED5:      MOV   BYTE PTR @STATUSREG,00011000b
               CALL  CLRDRIVETXT
               RETN
@WRITED3:      MOV   BYTE PTR @STATUSREG,10001100b
               OR    BYTE PTR [NMI],$80
               RETN
@WRITED1:      MOV   BYTE PTR @STATUSREG,00011000b
               MOV   WORD PTR @NMIHNDLR,OFFSET @NONMI
               CALL  CLRDRIVETXT
@NONMI:        RETN
@WRITED4:      MOV   AL,$16 {write error}
               CALL  @SAVEERRORNR
               RETN

{---[command13: read data variable length/multi-record format]--------------}
@COMMAND13:    MOV   WORD PTR @NMIHNDLR,OFFSET @READDAT
               CALL  @SETCMDDEST
               CALL  @CHKDRIVEREADY
               JC    @CMD13_1
               CALL  @GETDIFORDRIVE
               MOV   AL,BYTE PTR @PARAMETERS[$00]
               MOV   BYTE PTR @HEADPOS[DI],AL
               MOV   BYTE PTR @TRACK,AL
               MOV   AL,BYTE PTR @PARAMETERS[$01]
               MOV   BYTE PTR @SECTOR,AL
               MOV   AL,BYTE PTR @PARAMETERS[$02]
               MOV   CL,AL
               AND   AL,00011111b
               MOV   BYTE PTR @AANTALSECT,AL
               SHR   CL,5
               ADD   CL,$07
               MOV   AX,$0001
               SHL   AX,CL
               MOV   WORD PTR @BYTESPERSECT,AX
               CALL  @CHKLEGALPOS
               JC    @CMD13_1
               CALL  @SEEKFILEPOS
               JC    @CMD13_1
               MOV   WORD PTR @BUFPTR,0
               OR    BYTE PTR [NMI],$80
               MOV   BYTE PTR @STATUSREG,10001100b
               CALL  SETDRIVETXT
@CMD13_1:      RETN

@READDAT:      CALL  @CHECKERROR
               JC    @READD6
               CMP   BYTE PTR @AANTALSECT,$00
               JZ    @READD1
               MOV   SI,WORD PTR @BUFPTR
               OR    SI,SI
               JNZ   @READD2
               MOV   AH,$3F
               CALL  @GETFILEHANDLE
               JZ    @READD3
               MOV   CX,$0100
               MOV   DX,OFFSET @BUFFER
               PUSH  DS
               PUSH  CS
               POP   DS
               INT   $21 {---read data from disk image---}
               POP   DS
               JC    @READD3
               CMP   AX,$0100
               JNZ   @READD3
               MOV   SI,WORD PTR @BUFPTR
@READD2:       MOV   AL,BYTE PTR @BUFFER[SI]
               MOV   BYTE PTR @DATAREG,AL
               INC   SI
               MOV   WORD PTR @BUFPTR,SI
               MOV   BYTE PTR @RESULTREG,$00
               CMP   SI,WORD PTR @BYTESPERSECT
               JL    @READD4
               MOV   WORD PTR @BUFPTR,$0000
               DEC   BYTE PTR @AANTALSECT
               JZ    @READD5
               INC   BYTE PTR @SECTOR
               CALL  @CHKLEGALPOS
               JNC   @READD4
@READD6:       RETN
@READD5:       MOV   BYTE PTR @STATUSREG,10011100b
               OR    BYTE PTR [NMI],$80
               RETN
@READD4:       MOV   BYTE PTR @STATUSREG,10001100b
               OR    BYTE PTR [NMI],$80
               RETN
@READD1:       MOV   BYTE PTR @STATUSREG,00011000b
               MOV   WORD PTR @NMIHNDLR,OFFSET @NONMI
               CALL  CLRDRIVETXT
               RETN
@READD3:       MOV   AL,$1E {illegal track or sector / read error}
               CALL  @SAVEERRORNR
               RETN

{---[command1B: read ID command]--------------------------------------------}
@COMMAND1B:    MOV   WORD PTR @NMIHNDLR,OFFSET @READID
               CALL  @SETCMDDEST
               CALL  @CHKDRIVEREADY
               JC    @CMD1B_1
               CALL  @GETDIFORDRIVE
               MOV   AL,BYTE PTR @PARAMETERS[$00]
               MOV   BYTE PTR @HEADPOS[DI],AL
               MOV   BYTE PTR @TRACK,AL
               MOV   BYTE PTR @SECTOR,$00
               MOV   AL,BYTE PTR @PARAMETERS[$02]
               MOV   BYTE PTR @AANTALSECT,AL
               CALL  @CHKLEGALPOS
               JC    @CMD1B_1
               MOV   WORD PTR @BUFPTR,0
               OR    BYTE PTR [NMI],$80
               MOV   BYTE PTR @STATUSREG,10000000b
               CALL  SETDRIVETXT
@CMD1B_1:      RETN

@READID:       CALL  @CHECKERROR
               JC    @READID8
               CMP   BYTE PTR @AANTALSECT,$00
               JZ    @READID1
               MOV   SI,WORD PTR @BUFPTR
               OR    SI,SI
               JNZ   @READID2
               MOV   AL,BYTE PTR @TRACK
@READID2:      CMP   SI,+$01
               JNZ   @READID3
               MOV   AL,$00
@READID3:      CMP   SI,+$02
               JNZ   @READID4
               MOV   AL,BYTE PTR @SECTOR
@READID4:      CMP   SI,+$03
               JNZ   @READID5
               MOV   AL,$01
@READID5:      MOV   BYTE PTR @DATAREG,AL
               INC   SI
               MOV   WORD PTR @BUFPTR,SI
               CMP   SI,+$04
               JB    @READID6
               MOV   WORD PTR @BUFPTR,$0000
               DEC   BYTE PTR @AANTALSECT
               JZ    @READID7
               INC   BYTE PTR @SECTOR
               CALL  @CHKLEGALPOS
               JNC   @READID6
@READID8:      RETN
@READID7:      MOV   BYTE PTR @STATUSREG,10011100b
               OR    BYTE PTR [NMI],$80
               RETN
@READID6:      MOV   BYTE PTR @STATUSREG,10001100b
               OR    BYTE PTR [NMI],$80
               RETN
@READID1:      MOV   BYTE PTR @STATUSREG,00011000b
               MOV   WORD PTR @NMIHNDLR,OFFSET @NONMI
               CALL  CLRDRIVETXT
               RETN

{---[command1F: verify data and deleted data]-------------------------------}
@COMMAND1F:    MOV   WORD PTR @NMIHNDLR,OFFSET @VERIFYDAT
               CALL  @SETCMDDEST
               CALL  @CHKDRIVEREADY
               JC    @CMD1F_1
               CALL  @GETDIFORDRIVE
               MOV   AL,BYTE PTR @PARAMETERS[$00]
               MOV   BYTE PTR @HEADPOS[DI],AL
               MOV   BYTE PTR @STATUSREG,10000000b
               OR    BYTE PTR [NMI],$80
               CALL  SETDRIVETXT
@CMD1F_1:      RETN

@VERIFYDAT:    CALL  @CHECKERROR
               JC    @VERIFY1
               MOV   BYTE PTR @STATUSREG,00011000b
               MOV   BYTE PTR @RESULTREG,$00
               MOV   WORD PTR @NMIHNDLR,OFFSET @NONMI
               CALL  CLRDRIVETXT
@VERIFY1:      RETN

{---[command23: formattrack]------------------------------------------------}
@COMMAND23:    MOV   WORD PTR @NMIHNDLR,OFFSET @FORMATTRACK
               CALL  @SETCMDDEST
               CALL  @CHKDRIVEREADY
               JC    @CMD23_1
               CALL  @GETDIFORDRIVE
               CALL  @CHKWRITEPROT
               JC    @CMD23_1
               MOV   AL,BYTE PTR @PARAMETERS[$00]
               MOV   BYTE PTR @HEADPOS[DI],AL
               MOV   BYTE PTR @TRACK,AL
               MOV   BYTE PTR @SECTOR,$00
               MOV   AL,BYTE PTR @PARAMETERS[$02]
               MOV   CL,AL
               AND   AL,00011111b
               MOV   BYTE PTR @AANTALSECT,AL
               SHR   CL,5
               ADD   CL,$07
               MOV   AX,$0001
               SHL   AX,CL
               MOV   WORD PTR @BYTESPERSECT,AX
               CALL  @CHKLEGALPOS
               JC    @CMD23_1
               CALL  @SEEKFILEPOS
               JC    @CMD23_1
               MOV   WORD PTR @BUFPTR,0
               OR    BYTE PTR [NMI],$80
               MOV   BYTE PTR @STATUSREG,10001100b
               CALL  SETDRIVETXT
@CMD23_1:      RETN

@FORMATTRACK:  CALL  @CHECKERROR
               JC    @FORMAT6
               CMP   BYTE PTR @AANTALSECT,$00
               JZ    @FORMAT1
               MOV   SI,WORD PTR @BUFPTR
               INC   SI
               MOV   WORD PTR @BUFPTR,SI
               MOV   BYTE PTR @RESULTREG,$00
               CMP   SI,+$04
               JB    @FORMAT2
               MOV   SI,$00FE
@FORMAT3:      MOV   WORD PTR @BUFFER[SI],$E5E5
               SUB   SI,+$02
               JNS   @FORMAT3
               MOV   AH,$40
               CALL  @GETFILEHANDLE
               JZ    @FORMAT4
               MOV   CX,$0100
               MOV   DX,OFFSET @BUFFER
               PUSH  DS
               PUSH  CS
               POP   DS
               INT   $21 {---write data to disk image---}
               POP   DS
               JC    @FORMAT4
               MOV   WORD PTR @BUFPTR,$0000
               DEC   BYTE PTR @AANTALSECT
               JZ    @FORMAT5
               INC   BYTE PTR @SECTOR
               CALL  @CHKLEGALPOS
               JNC   @FORMAT2
@FORMAT6:      RETN
@FORMAT5:      MOV   BYTE PTR @STATUSREG,00010000b
               OR    BYTE PTR [NMI],$80
               RETN
@FORMAT2:      MOV   BYTE PTR @STATUSREG,10001100b
               OR    BYTE PTR [NMI],$80
               RETN
@FORMAT1:      MOV   BYTE PTR @STATUSREG,00011000b
               MOV   WORD PTR @NMIHNDLR,OFFSET @NONMI
               CALL  CLRDRIVETXT
               RETN
@FORMAT4:      MOV   AL,$16
               CALL  @SAVEERRORNR
               RETN

{---[command29: seektrack]--------------------------------------------------}
@COMMAND29:    MOV   WORD PTR @NMIHNDLR,OFFSET @SEEKTRACK
               CALL  @SETCMDDEST
               CALL  @CHKDRIVEREADY
               JC    @CMD29_1
               CALL  @GETDIFORDRIVE
               MOV   AL,BYTE PTR @PARAMETERS[$00]
               MOV   BYTE PTR @HEADPOS[DI],AL
               MOV   BYTE PTR @STATUSREG,10000000b
               OR    BYTE PTR [NMI],$80
               CALL  SETDRIVETXT
@CMD29_1:      RETN

@SEEKTRACK:    CALL  @CHECKERROR
               JC    @SEEKTR1
               MOV   BYTE PTR @STATUSREG,00011000b
               MOV   BYTE PTR @RESULTREG,$00
               CALL  CLRDRIVETXT
@SEEKTR1:      RETN

{---[command2C: read drive status]------------------------------------------}
@COMMAND2C:    CALL  @GETDIFORDRIVE
               MOV   AL,10000000b
               CMP   BYTE PTR [CS:CMDDEST+$01],$00
               JZ    @CMD2C_1
               OR    AL,01000000b {drive 1 ready}
@CMD2C_1:      CMP   BYTE PTR [CS:CMDDEST+$00],$00
               JZ    @CMD2C_2
               OR    AL,00000100b {drive 0 ready}
@CMD2C_2:      CMP   BYTE PTR @HEADPOS[DI],$00
               JNZ   @CMD2C_3
               OR    AL,00000010b {head on track 0}
@CMD2C_3:      PUSH  DS
               PUSH  AX
               MOV   AX,SEG WRITEPROTECT
               MOV   DS,AX
               MOV   AL,BYTE PTR WRITEPROTECT[DI]
               TEST  BYTE PTR [CS:DRVCTRLOUTP],00100000b
               JZ    @CMD2C_5
               SHR   AL,4
@CMD2C_5:      AND   AL,$01
               POP   AX
               POP   DS
               JZ    @CMD2C_4
               OR    AL,00001000b {disk write protected}
@CMD2C_4:      MOV   BYTE PTR @RESULTREG,AL
               OR    BYTE PTR @STATUSREG,00010000b
               RETN

{---[command3A: write register]---------------------------------------------}
@COMMAND3A:    CALL  @SETCMDDEST
               MOV   AX,WORD PTR @PARAMETERS[$00]
               CMP   AL,$06
               JNZ   @CMD3A_1
               MOV   BYTE PTR @FDCREG06,AH
               RETN
@CMD3A_1:      CMP   AL,$10
               JNZ   @CMD3A_2
               MOV   BYTE PTR @FDCREG10,AH
               RETN
@CMD3A_2:      CMP   AL,$11
               JNZ   @CMD3A_3
               MOV   BYTE PTR @FDCREG11,AH
               RETN
@CMD3A_3:      CMP   AL,$12
               JNZ   @CMD3A_4
               MOV   BYTE PTR @HEADPOS[$00],AH
               RETN
@CMD3A_4:      CMP   AL,$13
               JNZ   @CMD3A_5
               MOV   BYTE PTR @FDCREG13,AH
               RETN
@CMD3A_5:      CMP   AL,$14
               JNZ   @CMD3A_6
@CMD3A_7:      MOV   BYTE PTR @MODEREG,AH
               RETN
@CMD3A_6:      CMP   AL,$17
               JZ    @CMD3A_7
               CMP   AL,$18
               JNZ   @CMD3A_8
               MOV   BYTE PTR @FDCREG18,AH
               RETN
@CMD3A_8:      CMP   AL,$19
               JNZ   @CMD3A_9
               MOV   BYTE PTR @FDCREG19,AH
               RETN
@CMD3A_9:      CMP   AL,$22
               JNZ   @CMD3A_10
               MOV   BYTE PTR @FDCREG22,AH
               RETN
@CMD3A_10:     CMP   AL,$23
               JNZ   @CMD3A_11
               MOV   BYTE PTR [CS:DRVCTRLOUTP],AH
               MOV   WORD PTR [CS:CMDDEST],$0000
               TEST  AH,$40
               JZ    @CMD3A_12
               DEC   BYTE PTR [CS:CMDDEST+$00]
@CMD3A_12:     TEST  AH,$80
               JZ    @CMD3A_11
               DEC   BYTE PTR [CS:CMDDEST+$01]
@CMD3A_11:     RETN

{---[command3D: read register]----------------------------------------------}
@COMMAND3D:    CALL  @SETCMDDEST
               MOV   AL,BYTE PTR @PARAMETERS[$00]
               MOV   AH,BYTE PTR @FDCREG06
               CMP   AL,$06
               JZ    @CMD3D_1
               MOV   AH,BYTE PTR @FDCREG10
               CMP   AL,$10
               JZ    @CMD3D_1
               MOV   AH,BYTE PTR @FDCREG11
               CMP   AL,$11
               JZ    @CMD3D_1
               MOV   AH,BYTE PTR @HEADPOS[$00]
               CMP   AL,$12
               JZ    @CMD3D_1
               MOV   AH,BYTE PTR @FDCREG13
               CMP   AL,$13
               JZ    @CMD3D_1
               MOV   AH,BYTE PTR @MODEREG
               CMP   AL,$14
               JZ    @CMD3D_1
               CMP   AL,$17
               JZ    @CMD3D_1
               MOV   AH,BYTE PTR @FDCREG18
               CMP   AL,$18
               JZ    @CMD3D_1
               MOV   AH,BYTE PTR @FDCREG19
               CMP   AL,$19
               JZ    @CMD3D_1
               MOV   AH,BYTE PTR @HEADPOS[$01]
               CMP   AL,$1A
               JZ    @CMD3D_1
               MOV   AH,BYTE PTR @FDCREG22
               CMP   AL,$22
               JZ    @CMD3D_1
               MOV   AH,BYTE PTR [CS:DRVCTRLOUTP]
               CMP   AL,$23
               JNZ   @CMD3D_2
@CMD3D_1:      MOV   BYTE PTR @RESULTREG,AH
               OR    BYTE PTR @STATUSREG,00010000b
@CMD3D_2:      RETN
END;

{$f+}
PROCEDURE READ_FDC; ASSEMBLER;
ASM
               MOV   AH,$00
               CALL  CALL_FDC
END;

PROCEDURE WRITE_FDC; ASSEMBLER;
ASM;
               MOV   AH,$01
               CALL  CALL_FDC
END;

PROCEDURE FDC_NMI_HANDLER; ASSEMBLER;
ASM;
               PUSHA
               MOV   AH,$02
               CALL  CALL_FDC
               POPA
END;

PROCEDURE OPEN_DISK_IMAGE (DRIVENR:BYTE; NOWRITE:BOOLEAN); ASSEMBLER;
ASM;
               MOV   AL,BYTE PTR DRIVENR
               MOV   CL,+14
               MUL   CL
               MOV   SI,AX
               MOV   BL,BYTE PTR DISKETTENAMES[SI]
               MOV   BH,$00
               INC   SI
               MOV   WORD PTR DISKETTENAMES[SI+BX],'D.'
               MOV   WORD PTR DISKETTENAMES[SI+BX+$02],'KS'
               MOV   BYTE PTR DISKETTENAMES[SI+BX+$04],$00
               MOV   AH,$3D
               MOV   AL,$A0 {read only; no write access by others}
               TEST  BYTE PTR NOWRITE,$FF
               JNZ   @ODI2
               MOV   AL,$A2 {allow read and write; no write access by others}
@ODI2:         MOV   CL,$FF
               MOV   DX,SI
               ADD   DX,OFFSET DISKETTENAMES
               PUSH  SI
               INT   $21
               POP   SI
               JNC   @ODI1
               SUB   AX,AX
               MOV   BYTE PTR DISKETTENAMES[SI-$01],$00
@ODI1:         MOV   BL,BYTE PTR DRIVENR
               MOV   BH,$00
               SHL   BX,1
               MOV   WORD PTR FILEHANDLES[CS:BX],AX
END;

PROCEDURE CLOSE_DISK_IMAGE (DRIVENR:BYTE); ASSEMBLER;
ASM;
               MOV   BL,BYTE PTR DRIVENR
               MOV   BH,$00
               SHL   BX,1
               MOV   BX,WORD PTR FILEHANDLES[CS:BX]
               MOV   AH,$3E
               INT   $21
               MOV   BL,BYTE PTR DRIVENR
               MOV   BH,$00
               SHL   BX,1
               MOV   WORD PTR FILEHANDLES[CS:BX],$0000
               MOV   WORD PTR [CS:CMDDEST],$0000
END;

{INITIALISATION}
VAR I:BYTE;
BEGIN
  DUMMY := $00;
  FOR I := 0 TO 1 DO WRITEPROTECT[I] := $00;
  FOR I := 0 TO 3 DO DISKETTENAMES[I] := '';
END.