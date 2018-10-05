(***************************************************************************)
(*                                                                         *)
(*         AtomCom v1.10 (c) by Wouter Ras, Delft, Dec 97 - Mar 98         *)
(*         -------------------------------------------------------         *)
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

{$g+,f-,i-,r-,m 16384,80000,655360}
PROGRAM ATOMCOM;
USES DOS,CRT,HEXA;
CONST SAMPLESIZE = $2000;
      WAVE0 : ARRAY[0..94] OF SHORTINT =
              (  0, -4,-11,-17,-24,-30,-35,-38,-40,-42,
               -44,-45,-47,-49,-50,-52,-53,-53,-53,-53,
               -53,-52,-50,-47,-44,-41,-38,-37,-36,-34,
               -33,-32,-32,-32,-31,-31,-30,-28,-26,-23,
               -20,-18,-14,-11, -8, -4,  0,  4,  9, 14,
                19, 24, 29, 34, 38, 43, 48, 51, 53, 55,
                59, 61, 62, 63, 64, 66, 67, 66, 65, 65,
                64, 62, 60, 56, 53, 50, 47, 46, 45, 44,
                43, 42, 41, 40, 39, 38, 36, 33, 30, 27,
                23, 19, 16, 11,  6);

      WAVE1 : ARRAY[0..91] OF SHORTINT =
              (  0, -6,-13,-18,-22,-26,-30,-32,-33,-33,
               -34,-34,-34,-34,-33,-33,-32,-31,-27,-22,
               -17,-12, -6,  0,  7, 14, 21, 27, 30, 32,
                34, 36, 37, 38, 38, 38, 38, 38, 36, 34,
                32, 30, 27, 22, 15,  8,  0, -6,-11,-17,
               -22,-28,-32,-33,-34,-34,-35,-35,-35,-35,
               -34,-34,-32,-29,-25,-21,-17,-12, -6,  0,
                 8, 16, 22, 26, 39, 31, 34, 36, 37, 37,
                 36, 36, 36, 34, 32, 31, 29, 26, 21, 14,
                 8,  3);
      SILENCE    = $80;
      SILENCEMIN = $7C;
      SILENCEMAX = $84;
      MAXWAVE1   = +11;
      MINWAVE0   = +16;
      MAXWAVE0   = +21;

TYPE ATMBUFTYPE   = ARRAY[$0000..$FFF7] OF BYTE;
     DMABUFTYPE   = ARRAY[$0000..PRED(SAMPLESIZE)] OF BYTE;
     SPEEDTYPE    = (SCOS,FCOS);
     ATMHEADERREC = RECORD
                      ATOMNAME     : ARRAY[$00..$0F] OF BYTE;
                      STARTADDRESS : WORD;
                      EXECADDRESS  : WORD;
                      DATASIZE     : WORD;
                    END;

VAR DSPVERSION    : WORD;        {hi:major; lo:minor}
    IOPORT        : WORD;        {soundblaster i/o-port}
    IRQ           : BYTE;        {soundblaster irq number}
    DMA           : BYTE;        {soundblaster dma channel}
    SPEEDMODE     : SPEEDTYPE;   {fcos or scos}
    ATMBUF        : ^ATMBUFTYPE; {buffer containing .atm file}
    ATMSIZE       : WORD;        {size of .atm file}
    DMABUF        : ^DMABUFTYPE; {samplebuffer 1}
    DMABUFNR      : BYTE;        {buffernumber currently outputted to dsp}
    ATMBUFPTR     : WORD;        {pointer to data from/to atmbuffer}
    DMABUFPTR     : WORD;        {pointer to data from/to _NOT_ dmabuffer}
    WAVEPOS       : REAL;        {pointer to data retrieved from wave arrays}
    CHECKSUM      : BYTE;        {checksum for sending after datablock}
    IRQOCC        : BYTE;        {irq occurred? 00h=no; 01h=yes}
    ENDOFDATA     : BYTE;        {whether or not end of data has been reached}
    USERBREAK     : BOOLEAN;     {escape pressed?}
    FIRSTMAIN     : BOOLEAN;     {first time main menu called: don't clrscr}
    FIRSTWAVEDOWN : BOOLEAN;
    WAVELENGTH    : BYTE;
    ATMHEADER     : ATMHEADERREC;

PROCEDURE INPUTSTRING (LENGTE:BYTE;VAR S:STRING);
LABEL 1;
VAR CH,DH:CHAR;
    N,P:BYTE;
    XC,YC:BYTE;
    T:STRING;
BEGIN
  USERBREAK := FALSE;
  T := S;
1:S := T;
  XC := WHEREX;
  YC := WHEREY;
  P := SUCC(LENGTH(S));
  REPEAT
    WHILE LENGTH(S) < LENGTE DO S := S + '_';
    INLINE ($B8/$00/$01/$B9/$07/$26/$CD/$10); {---hidecursor---}
    GOTOXY (XC,YC);
    WRITE (S);
    GOTOXY (XC+PRED(P),YC);
    INLINE ($B8/$00/$01/$B9/$06/$05/$CD/$10); {---showcursor---}
    CH := READKEY;
    IF CH=#0 THEN
    BEGIN
      DH := READKEY;
      IF (DH=#75) AND (P>1) THEN DEC(P);
      IF (DH=#77) AND (P<=LENGTE) THEN INC(P);
      IF (DH=#83) AND (P<=LENGTE) THEN BEGIN
                                         DELETE (S,P,1);
                                         S := S + '_';
                                       END;
      IF (DH=#$75) AND (P<=LENGTE) THEN
      BEGIN
        FOR N := P TO LENGTE DO S[N] := '_';
      END;
      IF DH=#$47 THEN P := 1;
      IF DH=#$4F THEN BEGIN
                        P := SUCC(LENGTE);
                        WHILE S[PRED(P)]='_' DO DEC(P);
                      END;
    END;
    IF (CH=#8) AND (P>1) THEN BEGIN
                                DELETE (S,PRED(P),1);
                                S := S + '_';
                                DEC(P);
                              END;
    IF (CH>=' ') AND (P<=LENGTE) Then
    BEGIN
      DELETE (S,LENGTH(S),1);
      INSERT (CH,S,P);
      INC (P);
    END;
    IF CH=#27 THEN BEGIN
                     USERBREAK := TRUE;
                     EXIT;
                   END;
  UNTIL (CH=#13);
  WHILE S[LENGTH(S)] = '_' DO DELETE (S,LENGTH(S),1);
  IF S='' THEN GOTO 1;
  GOTOXY (XC,YC);
  WRITE (S);
  CLREOL;
END;

PROCEDURE RESETDSP; ASSEMBLER;
ASM;
               MOV   DX,WORD PTR IOPORT
               ADD   DL,$06
               MOV   AL,$01
               OUT   DX,AL
               MOV   CX,$0400
@RESDSP1:      NOP
               LOOP  @RESDSP1
               MOV   AL,$00
               OUT   DX,AL
               MOV   BL,$10
@RESDSP3:      MOV   DX,WORD PTR IOPORT
               ADD   DL,$0E
               MOV   CX,$0100
@RESDSP2:      IN    AL,DX
               TEST  AL,$80
               JNZ   @RESDSP4
               LOOP  @RESDSP2
               JMP   @RESDSP5
@RESDSP4:      SUB   DL,$04
               IN    AL,DX
               CMP   AL,$AA
               JZ    @RESDSP6
               DEC   BL
               JNZ   @RESDSP3
@RESDSP5:      MOV   WORD PTR IOPORT,$0000
@RESDSP6:
END;

PROCEDURE OUTBYTE; ASSEMBLER;
ASM;
               MOV   AH,AL
@OUTB1:        IN    AL,DX
               OR    AL,AL
               JS    @OUTB1
               MOV   AL,AH
               OUT   DX,AL
END;

PROCEDURE INBYTE; ASSEMBLER; {uitvoer AL=byte}
ASM;
               MOV   DX,WORD PTR IOPORT
               ADD   DL,$0E
@INB1:         IN    AL,DX
               OR    AL,AL
               JNS   @INB1
               SUB   DL,$04
               IN    AL,DX
END;

PROCEDURE STARTDMA (SEGM,ADRS:WORD;DIRECTION:BYTE); ASSEMBLER;
ASM; {direction=00h:from PC to ATOM; 01h:from ATOM to PC}
               {set samplerate}
               MOV   DX,WORD PTR IOPORT
               ADD   DL,$0C
               MOV   AL,$40
               CALL  OUTBYTE
               MOV   AL,$D2 {22050 Hz}
               CALL  OUTBYTE
               CMP   WORD PTR DSPVERSION,$0400
               JB    @SK1
               {set 8-bit, mono mode on SB16}
               MOV   AL,$C6
               CALL  OUTBYTE
               MOV   AL,$00
               CALL  OUTBYTE
@SK1:          {set dma blocksize}
               MOV   AL,$48
               CALL  OUTBYTE
               MOV   AL,((SAMPLESIZE SHR 1) - 1) AND $FF
               CALL  OUTBYTE
               MOV   AL,((SAMPLESIZE SHR 1) - 1) SHR 8
               CALL  OUTBYTE
               {enable speaker}
               MOV   AL,$D1
               CALL  OUTBYTE
               {setup dma}
               MOV   AL,BYTE PTR DMA
               OR    AL,$04
               OUT   $0A,AL
               MOV   AL,$00
               OUT   $0C,AL
               MOV   AL,$58
               CMP   BYTE PTR DIRECTION,$00
               JZ    @SK2
               MOV   AL,$54
@SK2:          OR    AL,BYTE PTR DMA
               OUT   $0B,AL
               MOV   AX,WORD PTR ADRS
               MOV   DX,WORD PTR SEGM
               ROL   DX,4
               MOV   CX,DX
               AND   DX,+$0F
               AND   CX,-$10
               ADD   AX,CX
               ADC   DX,+$00
               PUSH  DX
               MOV   DL,BYTE PTR DMA
               SHL   DL,1
               MOV   DH,$00
               OUT   DX,AL {address byte 0}
               MOV   AL,AH
               OUT   DX,AL {address byte 1}
               INC   DX
               MOV   AL,(SAMPLESIZE - 1) AND $FF
               OUT   DX,AL {byte count lo}
               MOV   AL,(SAMPLESIZE - 1) SHR 8
               OUT   DX,AL {byte count hi}
               MOV   BL,BYTE PTR DMA
               MOV   BH,$00
               MOV   DL,BYTE PTR @PAGENR[CS:BX]
               MOV   DH,$00
               POP   AX
               OUT   DX,AL {address byte 2}
               MOV   AL,BYTE PTR DMA
               OUT   $0A,AL
               {perform auto-init}
               MOV   DX,WORD PTR IOPORT
               ADD   DL,$0C
               MOV   AL,$1C
               CMP   BYTE PTR DIRECTION,$00
               JZ    @SK3
               MOV   AL,$2C
@SK3:          CALL  OUTBYTE
               JMP   @ENDOFPROC
@PAGENR:       DB    $87,$83,$81,$82
@ENDOFPROC:
END;

PROCEDURE IRQVECTOR (ZETTEN:BYTE); ASSEMBLER;
ASM;
               MOV   BL,BYTE PTR IRQ
               TEST  BL,$08
               JZ    @SETCLRIRQ2
               AND   BL,$07
               ADD   BL,$70
               JMP   @SETCLRIRQ1
@SETCLRIRQ2:   ADD   BL,$08
@SETCLRIRQ1:   MOV   BH,$00
               SHL   BX,2
               SUB   AX,AX
               MOV   ES,AX
               TEST  BYTE PTR ZETTEN,$FF
               JZ    @CLRIRQVEC
               CLI
               MOV   AX,WORD PTR [ES:BX]
               MOV   WORD PTR @ORGIRQVEC[CS:$00],AX
               MOV   AX,WORD PTR [ES:BX+$02]
               MOV   WORD PTR @ORGIRQVEC[CS:$02],AX
               MOV   AX,OFFSET @IRQHANDLER
               MOV   WORD PTR [ES:BX],AX
               MOV   WORD PTR [ES:BX+$02],CS
               STI
               JMP   @ENDOFPROC
@CLRIRQVEC:    CLI
               MOV   AX,WORD PTR @ORGIRQVEC[CS:$00]
               MOV   WORD PTR [ES:BX],AX
               MOV   AX,WORD PTR @ORGIRQVEC[CS:$02]
               MOV   WORD PTR [ES:BX+$02],AX
               STI
               JMP   @ENDOFPROC

@IRQHANDLER:   PUSH  DS
               PUSH  DX
               PUSH  AX
               MOV   AX,SEG IOPORT
               MOV   DS,AX
               MOV   DX,WORD PTR IOPORT
               ADD   DL,$0E
               IN    AL,DX
               CMP   BYTE PTR ENDOFDATA,$01
               JB    @IRQH2
               INC   BYTE PTR ENDOFDATA
@IRQH2:        XOR   BYTE PTR DMABUFNR,$03
               MOV   BYTE PTR IRQOCC,$01
               MOV   AL,$20
               CMP   BYTE PTR IRQ,$07
               JBE   @IRQH1
               OUT   $A0,AL
@IRQH1:        OUT   $20,AL
               POP   AX
               POP   DX
               POP   DS
               IRET
@ORGIRQVEC:    DD    $00000000
@ENDOFPROC:
END;

PROCEDURE CLRIRQMASK; ASSEMBLER;
ASM;
               MOV   DX,$0021
               MOV   CL,BYTE PTR IRQ
               TEST  CL,$08
               JZ    @SETMASK1
               AND   CL,$07
               MOV   DL,$A1
@SETMASK1:     MOV   AH,$01
               SHL   AH,CL
               NOT   AH
               IN    AL,DX
               AND   AL,AH
               OUT   DX,AL
END;

PROCEDURE SETIRQMASK; ASSEMBLER;
ASM;
               MOV   DX,$0021
               MOV   CL,BYTE PTR IRQ
               TEST  CL,$08
               JZ    @CLRMASK1
               AND   CL,$07
               MOV   DL,$A1
@CLRMASK1:     MOV   AH,$01
               SHL   AH,CL
               IN    AL,DX
               OR    AL,AH
               OUT   DX,AL
END;

PROCEDURE STOPDMA; ASSEMBLER;
ASM;
               MOV   DX,WORD PTR IOPORT
               ADD   DL,$0C
               {disable speaker}
               MOV   AL,$D3
               CALL  OUTBYTE
               {halt dma}
               MOV   AL,$D0
               CALL  OUTBYTE
               {exit auto-init mode}
               MOV   AL,$DA
               CALL  OUTBYTE
               {halt dma}
               MOV   AL,$D0
               CALL  OUTBYTE
END;

FUNCTION HEX2DEC (S:STRING):WORD;
VAR I:BYTE;
BEGIN
  FOR I := 1 TO LENGTH(S) DO S[I] := UPCASE(S[I]);
  WHILE LENGTH(S) < 4 DO S := '0' + S;
  FOR I := 1 TO 4 DO
  BEGIN
    DEC (S[I],48);
    IF ORD(S[I]) > 9 THEN DEC (S[I],7);
  END;
  HEX2DEC := SWAP((ORD(S[1]) SHL 4) + ORD(S[2])) +
             (ORD(S[3]) SHL 4) + ORD(S[4]);
END;

PROCEDURE INITBLASTER;
VAR S,T:STRING[80];
    I,J:BYTE;
    CODE:INTEGER;
    PS,IS,DS:BOOLEAN;
BEGIN
  PS := FALSE;
  IS := FALSE;
  DS := FALSE;
  S := GETENV ('BLASTER');
  FOR I := 1 TO LENGTH(S) DO S[I] := UPCASE(S[I]);
  WHILE (LENGTH(S) > 0) DO
  BEGIN
    IF (S[1]='A') OR (S[1]='I') OR (S[1]='D') THEN
    BEGIN
      T := '';
      I := 2;
      WHILE (I <= LENGTH(S)) AND (S[I] <> ' ') DO
      BEGIN
        T := T + S[I];
        INC (I);
      END;
      IF S[1] = 'A' THEN
      BEGIN
        IOPORT := HEX2DEC (T);
        PS := TRUE;
      END;
      IF S[1] = 'I' THEN
      BEGIN
        VAL (T,IRQ,CODE);
        IF CODE=0 THEN IS := TRUE;
      END;
      IF S[1] = 'D' THEN
      BEGIN
        VAL (T,DMA,CODE);
        IF CODE=0 THEN DS := TRUE;
      END;
      DELETE (S,1,I);
    END ELSE
    BEGIN
      DELETE (S,1,1);
    END;
  END;
  IF NOT (PS AND IS AND DS) THEN
  BEGIN
    WRITELN ('Blaster environment string not set or not set correctly. Program aborted.');
    HALT;
  END;
  WRITELN ('Soundcard detected at I/O-port    ',HEXW(IOPORT),'h');
  WRITELN ('                      IRQ-number  ',IRQ);
  WRITELN ('                      DMA-channel ',DMA);
  RESETDSP;
  IF IOPORT = $0000 THEN
  BEGIN
    WRITELN ('Cannot initialize SoundBlaster. Program aborted.');
    HALT;
  END;
  ASM;
               MOV   DX,WORD PTR IOPORT
               ADD   DL,$0C
               MOV   AL,$E1
               CALL  OUTBYTE
               CALL  INBYTE
               MOV   AH,AL
               CALL  INBYTE
               MOV   WORD PTR DSPVERSION,AX
  END;
  WRITE ('Card type: SoundBlaster ');
  CASE HI(DSPVERSION) OF 1: WRITE;
                         2: WRITE ('2');
                         3: WRITE ('Pro');
                       ELSE WRITE ('16');
  END;
  WRITELN (' or clone');
  WRITE ('           DSP-version ',HI(DSPVERSION),'.');
  IF LO(DSPVERSION) < 10 THEN WRITE ('0');
  WRITELN (LO(DSPVERSION));
  WRITELN;
  IF HI(DSPVERSION) <= 1 THEN
  BEGIN
    WRITELN ('Sorry, this card cannot handle "auto-init" mode. Program aborted.');
    HALT;
  END;
  FIRSTMAIN := TRUE;
END;

{---[main menu]-------------------------------------------------------------}
PROCEDURE MAINMENU (VAR SELECTION:BYTE);
VAR CH:CHAR;
BEGIN
  IF NOT FIRSTMAIN THEN CLRSCR
                   ELSE FIRSTMAIN := FALSE;
  TEXTCOLOR (LIGHTCYAN);
  WRITELN ('M A I N   M E N U');
  TEXTCOLOR (CYAN);
  WRITELN;
  WRITELN ('1   : Transfer data from PC to ATOM,');
  WRITELN ('2   : Transfer data from ATOM to PC,');
  WRITELN ('Esc : Return to OS.');
  TEXTCOLOR (LIGHTGRAY);
  WHILE KEYPRESSED DO CH := READKEY;
  REPEAT
    CH := READKEY;
    IF CH=#27 THEN HALT;
  UNTIL (CH >= '1') AND (CH <= '2');
  SELECTION := ORD(CH)-48;
  WRITELN;
END;

{---[data from pc to atom]--------------------------------------------------}
FUNCTION BUFHALF:WORD;
BEGIN
  IF DMABUFNR = 1 THEN BUFHALF := SIZEOF(DMABUFTYPE) SHR 1
                  ELSE BUFHALF := 0;
END;

PROCEDURE WAITFORDMA; {buffer filled, wait until other buffer is free}
VAR CH:CHAR;
BEGIN
  DMABUFPTR := $0000;
  REPEAT
    IF KEYPRESSED THEN
    BEGIN
      CH := READKEY;
      IF CH = #27 THEN USERBREAK := TRUE;
      WHILE KEYPRESSED DO CH := READKEY;
    END;
  UNTIL (IRQOCC <> $00) OR USERBREAK;
  IRQOCC := $00;
END;

PROCEDURE WRITEWAVE (BIT:BYTE);
VAR I,AANT:BYTE;
BEGIN
  IF SPEEDMODE = SCOS THEN AANT := 4
                      ELSE AANT := 1;
  IF BIT=0 THEN
  BEGIN
    FOR I := 1 TO AANT DO
    BEGIN
      WHILE (ROUND(WAVEPOS) < SIZEOF(WAVE0)) AND (NOT USERBREAK) DO
      BEGIN
        DMABUF^[BUFHALF+DMABUFPTR] := $80 - WAVE0[ROUND(WAVEPOS)];
        WAVEPOS := WAVEPOS + SIZEOF(WAVE0)/(22050/1200);
        INC (DMABUFPTR);
        IF DMABUFPTR >= (SIZEOF(DMABUFTYPE) SHR 1) THEN WAITFORDMA;
      END;
      WAVEPOS := WAVEPOS - SIZEOF(WAVE0);
    END;
  END ELSE
  BEGIN
    FOR I := 1 TO AANT DO
    BEGIN
      WHILE (ROUND(WAVEPOS) < SIZEOF(WAVE1)) AND (NOT USERBREAK) DO
      BEGIN
        DMABUF^[BUFHALF+DMABUFPTR] := $80 - WAVE1[ROUND(WAVEPOS)];
        WAVEPOS := WAVEPOS + SIZEOF(WAVE1)/(22050/1200);
        INC (DMABUFPTR);
        IF DMABUFPTR >= (SIZEOF(DMABUFTYPE) SHR 1) THEN WAITFORDMA;
      END;
      WAVEPOS := WAVEPOS - SIZEOF(WAVE1);
    END;
  END;
END;

PROCEDURE WRITEBYTE (BT:BYTE);
VAR I:WORD;
BEGIN
  CHECKSUM := (CHECKSUM + BT) AND $FF;
  WRITEWAVE (0); {---startbit---}
  I := $01;
  WHILE I < $0100 DO
  BEGIN
    IF BT AND I <> $00 THEN WRITEWAVE (1)
                       ELSE WRITEWAVE (0);
    I := I SHL 1;
  END;
  WRITEWAVE (1); {---stopbit---}
  {---extra half wave1---}
  WHILE (ROUND(WAVEPOS) < 46) AND (NOT USERBREAK) DO
  BEGIN
    DMABUF^[BUFHALF+DMABUFPTR] := $80 - WAVE1[ROUND(WAVEPOS)];
    WAVEPOS := WAVEPOS + SIZEOF(WAVE1)/(22050/1200);
    INC (DMABUFPTR);
    IF DMABUFPTR >= (SIZEOF(DMABUFTYPE) SHR 1 ) THEN WAITFORDMA;
  END;
  WAVEPOS := WAVEPOS - 46;
END;

PROCEDURE LOADSOURCEFILE;
VAR FROMF:FILE;
    SOURCEFILENAME:STRING;
    I:BYTE;
    CH:CHAR;
BEGIN
  WRITE ('Name of .ATM-file ? ');
  SOURCEFILENAME := '';
  INPUTSTRING (59,SOURCEFILENAME);
  IF USERBREAK THEN EXIT;
  WRITELN;
  WRITELN;
  FOR I := 1 TO LENGTH(SOURCEFILENAME) DO
    SOURCEFILENAME[I] := UPCASE(SOURCEFILENAME[I]);
  IF COPY(SOURCEFILENAME,LENGTH(SOURCEFILENAME)-3,4) <> '.ATM' THEN
    SOURCEFILENAME := SOURCEFILENAME + '.ATM';
  ASSIGN (FROMF,SOURCEFILENAME);
  RESET (FROMF,1);
  IF IORESULT <> 0 THEN
  BEGIN
    WRITELN (SOURCEFILENAME,' not found.');
    WHILE KEYPRESSED DO CH := READKEY;
    CH := READKEY;
    WHILE KEYPRESSED DO CH := READKEY;
    USERBREAK := TRUE;
    EXIT;
  END;
  ATMSIZE := FILESIZE(FROMF);
  BLOCKREAD (FROMF,ATMBUF^,ATMSIZE);
  CLOSE (FROMF);
END;

PROCEDURE PC_TO_ATOM;
LABEL 1,2,3;
VAR CH:CHAR;
    I:WORD;
    BLOCKNUMBER:BYTE;
    NUMBYTES:WORD;
    STARTADDRESS:WORD;
    ENDADDRESS:WORD;
    W:WORD;
    S:STRING;
BEGIN
  TEXTCOLOR (YELLOW);
  I := 0;
  WHILE (I < 16) AND (ATMBUF^[I] <> $00) DO
  BEGIN
    WRITE (CHR(ATMBUF^[I]));
    INC (I);
  END;
  WHILE WHEREX < 18 DO WRITE (' ');
  STARTADDRESS := ATMBUF^[$10] + SWAP(ATMBUF^[$11]);
  ENDADDRESS := ATMBUF^[$14] + SWAP(ATMBUF^[$15]) + STARTADDRESS;
  WRITE (HEXW(STARTADDRESS),' ',HEXW(ENDADDRESS),' ');
  WRITELN (HEXW(ATMBUF^[$12]+SWAP(ATMBUF^[$13])));
  TEXTCOLOR (LIGHTGRAY);
  WRITE ('Use SLOW or FAST tape interface [S/F] ? ');
  IF SPEEDMODE = SCOS THEN WRITE ('S')
                      ELSE WRITE ('F');
  WRITE (#8);
  WHILE KEYPRESSED DO CH := READKEY;
  REPEAT
    CH := UPCASE(READKEY);
    IF CH=#27 THEN GOTO 1;
    IF CH=#13 THEN IF SPEEDMODE = SCOS THEN CH := 'S'
                                       ELSE CH := 'F';
  UNTIL (CH='S') OR (CH='F');
  WRITELN (CH);
  IF CH='S' THEN SPEEDMODE := SCOS
            ELSE SPEEDMODE := FCOS;
2:GOTOXY (1,WHEREY);
  WRITE ('Start at ? ');
  CLREOL;
  S := HEXW(STARTADDRESS);
  INPUTSTRING (4,S);
  IF USERBREAK THEN GOTO 1;
  W := HEX2DEC (S);
  IF (W < STARTADDRESS) OR (W >= ENDADDRESS) THEN GOTO 2;
  STARTADDRESS := W;
  WRITELN ('h');
3:GOTOXY (1,WHEREY);
  WRITE ('End at ? ');
  CLREOL;
  S := HEXW(ENDADDRESS);
  INPUTSTRING (4,S);
  IF USERBREAK THEN GOTO 1;
  W := HEX2DEC (S);
  IF (W <= STARTADDRESS) OR (W > ENDADDRESS) THEN GOTO 3;
  ENDADDRESS := W;
  WRITELN ('h');
  WRITELN;
  USERBREAK := FALSE;
  ENDOFDATA := $00;
  IRQOCC := $00;
  DMABUFNR := 1;
  DMABUFPTR := $0000;
  ATMBUFPTR := $0016;
  W := STARTADDRESS - (ATMBUF^[$10] + SWAP(ATMBUF^[$11]));
  MOVE (ATMBUF^[$0016+W],ATMBUF^[$0016],ATMSIZE-W);
  ATMSIZE := $0016 + ENDADDRESS - STARTADDRESS;
  WAVEPOS := 0;
  FILLCHAR (DMABUF^,SIZEOF(DMABUFTYPE),$80);
  BLOCKNUMBER := $00;
  IRQVECTOR (1);
  CLRIRQMASK;
  STARTDMA (SEG(DMABUF^),OFS(DMABUF^),$00);
  TEXTCOLOR (WHITE);
  WRITE ('Send status:');
  TEXTCOLOR (LIGHTGRAY);
  WHILE (ATMBUFPTR < ATMSIZE) AND (NOT USERBREAK) DO
  BEGIN
    NUMBYTES := $0100;
    IF ATMSIZE - ATMBUFPTR < $0100 THEN NUMBYTES := ATMSIZE - ATMBUFPTR;
    FOR I := 1 TO 1200 DO WRITEWAVE (1);
    WRITELN;
    FOR I := 0 TO 15 DO
    BEGIN
      IF ATMBUF^[I] = $00 THEN WRITE (' ')
                          ELSE WRITE (CHR(ATMBUF^[I]));
    END;
    I := STARTADDRESS + SWAP(BLOCKNUMBER);
    WRITE (' ',HEXW(I),' ',HEXW(I+PRED(NUMBYTES)));
    WRITE (' ',HEXW(SWAP(ATMBUF^[$13])+ATMBUF^[$12]));
    WRITE (' ',HEX(BLOCKNUMBER));
    CLREOL;
    {---write control block---}
    CHECKSUM := $00;
    FOR I := 1 TO 4 DO WRITEBYTE (ORD('*'));
    I := 0;
    WHILE (I < 16) AND (ATMBUF^[I] <> $00) DO
    BEGIN
      WRITEBYTE (ATMBUF^[I]);
      INC (I);
    END;
    WRITEBYTE ($0D);
    {---last block?---}
    IF ATMBUFPTR + 256 >= ATMSIZE THEN WRITEBYTE ($7F)
                                  ELSE WRITEBYTE ($FF);
    WRITEBYTE ($00);
    WRITEBYTE (BLOCKNUMBER);
    WRITEBYTE (PRED(NUMBYTES));
    WRITEBYTE (ATMBUF^[$13]);
    WRITEBYTE (ATMBUF^[$12]);
    WRITEBYTE (HI(STARTADDRESS + SWAP(BLOCKNUMBER)));
    WRITEBYTE (LO(STARTADDRESS));
    IF SPEEDMODE = SCOS THEN FOR I := 1 TO 240 DO WRITEWAVE (1)
                        ELSE FOR I := 1 TO 300 DO WRITEWAVE (1);
    {---write datablock---}
    FOR I := 0 TO PRED(NUMBYTES) DO WRITEBYTE (ATMBUF^[ATMBUFPTR+I]);
    INC (ATMBUFPTR,NUMBYTES);
    {---write checksum---}
    WRITEBYTE (CHECKSUM);
    INC (BLOCKNUMBER);
  END;
  WRITEWAVE (1);
  FILLCHAR (DMABUF^[BUFHALF+DMABUFPTR],(SIZEOF(DMABUFTYPE) SHR 1)-DMABUFPTR,$80);
  ENDOFDATA := $01;
  REPEAT UNTIL (ENDOFDATA = $03) OR USERBREAK;
  STOPDMA;
  SETIRQMASK;
  IRQVECTOR (0);
1:GOTOXY (1,WHEREY);
  IF USERBREAK THEN WRITE ('User break.')
               ELSE WRITE ('Transfer ended.');
  CLREOL;
  WRITELN;
END;

{---[data from atom to pc]--------------------------------------------------}
FUNCTION GETBYTE:BYTE;
VAR CH:CHAR;
BEGIN
  IF USERBREAK THEN EXIT;
  IF DMABUFPTR >= (SIZEOF(DMABUFTYPE) SHR 1) THEN
  BEGIN
    DMABUFPTR := $0000;
    REPEAT
      IF KEYPRESSED THEN
      BEGIN
        CH := READKEY;
        IF CH = #27 THEN USERBREAK := TRUE;
        WHILE KEYPRESSED DO CH := READKEY;
      END;
    UNTIL (IRQOCC <> $00) OR USERBREAK;
    IRQOCC := $00;
  END;
  GETBYTE := DMABUF^[BUFHALF+DMABUFPTR];
  INC (DMABUFPTR);
  INC (WAVELENGTH);
END;

PROCEDURE SEEKENDOFWAVE;
BEGIN
  WAVELENGTH := 0;
  IF FIRSTWAVEDOWN THEN
  BEGIN
    REPEAT
      IF USERBREAK THEN EXIT;
    UNTIL GETBYTE > SILENCE;
    REPEAT
      IF USERBREAK THEN EXIT;
    UNTIL (GETBYTE < SILENCE) OR (WAVELENGTH = $FF);
    IF (WAVELENGTH > MAXWAVE1) AND (WAVELENGTH < MINWAVE0) THEN
    BEGIN
      REPEAT
        IF USERBREAK THEN EXIT;
      UNTIL GETBYTE > SILENCE;
      WAVELENGTH := (MINWAVE0 + MAXWAVE0) DIV 2;
      FIRSTWAVEDOWN := FALSE;
    END;
  END ELSE
  BEGIN
    REPEAT
      IF USERBREAK THEN EXIT;
    UNTIL GETBYTE < SILENCE;
    REPEAT
      IF USERBREAK THEN EXIT;
    UNTIL (GETBYTE > SILENCE) OR (WAVELENGTH = $FF);
    IF (WAVELENGTH > MAXWAVE1) AND (WAVELENGTH < MINWAVE0) THEN
    BEGIN
      REPEAT
        IF USERBREAK THEN EXIT;
      UNTIL GETBYTE < SILENCE;
      WAVELENGTH := (MINWAVE0 + MAXWAVE0) DIV 2;
      FIRSTWAVEDOWN := TRUE;
    END;
  END;
END;

FUNCTION READONEATMBYTE (FIRSTWAVEDONE:BOOLEAN):BYTE;
VAR DATABITS:ARRAY[0..9] OF BYTE;
    S:STRING[16];
    I:BYTE;
BEGIN
  I := 0;
  DATABITS[0] := 0;
  S := '';
  IF SPEEDMODE = SCOS THEN
  BEGIN
    IF FIRSTWAVEDONE THEN S := '00';
  END ELSE
  BEGIN
    IF FIRSTWAVEDONE THEN I := 1;
  END;
  WHILE I <= 9 DO
  BEGIN
    SEEKENDOFWAVE;
    IF WAVELENGTH <= MAXWAVE1 THEN
    BEGIN
      S := S + '1';
    END ELSE
      IF WAVELENGTH >= MINWAVE0 THEN
      BEGIN
        S := S + '00';
      END;
    IF ((SPEEDMODE = FCOS) AND (S='00')) OR
       ((SPEEDMODE = SCOS) AND (S='00000000')) THEN
    BEGIN
      DATABITS[I] := 0;
      INC (I);
      S := '';
    END ELSE
      IF ((SPEEDMODE = FCOS) AND (S='11')) OR
         ((SPEEDMODE = SCOS) AND (S='11111111')) THEN
      BEGIN
        DATABITS[I] := 1;
        INC (I);
        S := '';
      END;
    IF ((SPEEDMODE = FCOS) AND (LENGTH(S) > 2)) OR
       ((SPEEDMODE = SCOS) AND (LENGTH(S) > 8)) THEN
    BEGIN
      GOTOXY (1,WHEREY);
      WRITELN ('Error: Misformed wave pattern.');
      USERBREAK := TRUE;
      EXIT;
    END;
  END;
  SEEKENDOFWAVE; {stopbit always has one extra wave}
  IF DATABITS[0] <> 0 THEN
  BEGIN
    GOTOXY (1,WHEREY);
    WRITELN ('Error: No startbit (0) found.');
    USERBREAK := TRUE;
    EXIT;
  END;
  IF DATABITS[9] <> 1 THEN
  BEGIN
    GOTOXY (1,WHEREY);
    WRITELN ('Error: No stopbit (1) found.');
    USERBREAK := TRUE;
    EXIT;
  END;
  ASM;
               MOV   DI,$0001
  @LP1:        SHR   BYTE PTR DATABITS[DI],1
               RCR   AL,1
               INC   DI
               CMP   DI,+$09
               JB    @LP1
               MOV   BYTE PTR I,AL
  END;
  READONEATMBYTE := I;
END;

FUNCTION READFIRSTBYTEHEADER:BOOLEAN;
CONST NIL_FAST = '00';
      NIL_SLOW = '00000000';
      ONE_FAST = '11';
      ONE_SLOW = '11111111';
      ASTERISK_FAST = NIL_FAST +
                      NIL_FAST + ONE_FAST + NIL_FAST + ONE_FAST +
                      NIL_FAST + ONE_FAST + NIL_FAST + NIL_FAST +
                      ONE_FAST + '1';
      ASTERISK_SLOW = NIL_SLOW +
                      NIL_SLOW + ONE_SLOW + NIL_SLOW + ONE_SLOW +
                      NIL_SLOW + ONE_SLOW + NIL_SLOW + NIL_SLOW +
                      ONE_SLOW + '1';
VAR S:STRING;
BEGIN
  S := '00';
  REPEAT
    SEEKENDOFWAVE;
    IF WAVELENGTH <= MAXWAVE1 THEN
    BEGIN
      S := S + '1';
    END ELSE
      IF WAVELENGTH >= MINWAVE0 THEN
      BEGIN
        S := S + '00';
      END;
    IF S = ASTERISK_FAST THEN
    BEGIN
      SPEEDMODE := FCOS;
      READFIRSTBYTEHEADER := TRUE;
      EXIT;
    END;
    IF S = ASTERISK_SLOW THEN
    BEGIN
      SPEEDMODE := SCOS;
      READFIRSTBYTEHEADER := TRUE;
      EXIT;
    END;
  UNTIL (LENGTH(S) > LENGTH(ASTERISK_SLOW)) OR USERBREAK;
  READFIRSTBYTEHEADER := FALSE;
END;

PROCEDURE ATOM_TO_PC;
LABEL 1,2,3,4;
VAR HEADER:ARRAY[$00..$FF] OF BYTE;
    HP:BYTE;
    NUMBYTES:WORD;
    I:BYTE;
    W:WORD;
    EERSTE:BOOLEAN;
    LASTBLOCK:BOOLEAN;
    TOF:FILE;
    STARTOFBLOCK:WORD;
    CH:CHAR;
    DESTFILENAME:STRING;
BEGIN
  USERBREAK := FALSE;
  ENDOFDATA := $00;
  IRQOCC := $00;
  DMABUFNR := 1;
  DMABUFPTR := $0000;
  ATMBUFPTR := $0000;
  FILLCHAR (DMABUF^,SIZEOF(DMABUFTYPE),$80);
  IRQVECTOR (1);
  CLRIRQMASK;
  IF HI(DSPVERSION) >= 3 THEN
  BEGIN
    ASM;
               MOV   DX,WORD PTR IOPORT
               ADD   DL,$04
               MOV   AL,$0C
               OUT   DX,AL
               INC   DX
               IN    AL,DX
               OR    AL,00000110b
               OUT   DX,AL
    END;
  END;
  IF HI(DSPVERSION) >= 4 THEN
  BEGIN
    ASM;
               MOV   DX,WORD PTR IOPORT
               ADD   DL,$04
               MOV   AL,$3D
               OUT   DX,AL
               INC   DX
               MOV   AL,00011000b
               OUT   DX,AL
               DEC   DX
               MOV   CX,$0200
    @LP1:      NOP
               LOOP  @LP1
               MOV   AL,$3E
               OUT   DX,AL
               INC   DX
               MOV   AL,00011000b
               OUT   DX,AL
    END;
  END;
  STARTDMA (SEG(DMABUF^),OFS(DMABUF^),$01);
  TEXTCOLOR (WHITE);
  WRITELN ('Receive status:');
  TEXTCOLOR (LIGHTGRAY);
2:STARTOFBLOCK := ATMBUFPTR;
  FIRSTWAVEDOWN := FALSE;
  WRITE ('Waiting for control block...');
  REPEAT
    SEEKENDOFWAVE;
    IF USERBREAK THEN GOTO 1;
  UNTIL (WAVELENGTH > MAXWAVE1) AND (WAVELENGTH <= MAXWAVE0);
  GOTOXY (1,WHEREY);
  IF NOT READFIRSTBYTEHEADER THEN GOTO 2;
  WRITE ('Receiving control block...');
  CLREOL;
  HEADER[0] := $2A;
  HP := 1;
  CHECKSUM := $2A;
  REPEAT
    HEADER[HP] := READONEATMBYTE (FALSE);
    IF USERBREAK THEN GOTO 1;
    CHECKSUM := LO(CHECKSUM + HEADER[HP]);
    INC (HP);
  UNTIL ((HP >= $0D) AND (HEADER[HP-$09] = $0D)) OR (HP >= $80);
  GOTOXY (1,WHEREY);
  IF (HEADER[$00] <> ORD('*')) OR (HEADER[$01] <> ORD('*')) OR
     (HEADER[$02] <> ORD('*')) OR (HEADER[$03] <> ORD('*')) THEN
  BEGIN
    WRITELN ('Error: Control block corrupted.');
    USERBREAK := TRUE;
    GOTO 1;
  END;
  I := $04;
  WHILE HEADER[I] <> $0D DO
  BEGIN
    WRITE (CHR(HEADER[I]));
    ATMHEADER.ATOMNAME[I-$04] := HEADER[I];
    INC (I);
  END;
  INC (I);
  WHILE WHEREX < 17 DO WRITE (' ');
  W := HEADER[I+$07] + (WORD(HEADER[I+$06]) SHL 8);
  IF HEADER[I+$02] = $00 THEN ATMHEADER.STARTADDRESS := W;
  WRITE (HEXW(W),' ');
  NUMBYTES := SUCC(WORD(HEADER[I+$03]));
  INC (W,PRED(NUMBYTES));
  WRITE (HEXW(W),' ');
  W := HEADER[I+$05] + (WORD(HEADER[I+$04]) SHL 8);
  IF HEADER[I+$02] = $00 THEN ATMHEADER.EXECADDRESS := W;
  WRITE (HEXW(W),'  ');
  W := HEADER[I+$02];
  WRITELN (HEX(W));
  W := HEADER[I];
  IF W AND $80 = $00 THEN LASTBLOCK := TRUE
                     ELSE LASTBLOCK := FALSE;
  {---searching datablock---}
  FIRSTWAVEDOWN := FALSE;
  WRITE ('Waiting for data block...');
  REPEAT
    SEEKENDOFWAVE;
    IF USERBREAK THEN GOTO 1;
  UNTIL (WAVELENGTH > MAXWAVE1) AND (WAVELENGTH <= MAXWAVE0);
  {---read datablock---}
  GOTOXY (1,WHEREY);
  WRITE ('Receiving data block...');
  CLREOL;
  EERSTE := TRUE;
  FOR W := 1 TO NUMBYTES DO
  BEGIN
    ATMBUF^[ATMBUFPTR] := READONEATMBYTE (EERSTE);
    EERSTE := FALSE;
    IF USERBREAK THEN GOTO 1;
    CHECKSUM := LO(CHECKSUM + ATMBUF^[ATMBUFPTR]);
    INC (ATMBUFPTR);
  END;
  I := READONEATMBYTE (FALSE); {---checksum---}
  GOTOXY (1,WHEREY);
  CLREOL;
  IF I <> CHECKSUM THEN
  BEGIN
    WRITELN ('Checksum error: ',HEX(CHECKSUM),'h must be ',HEX(I),'h.');
    USERBREAK := TRUE;
    GOTO 1;
  END;
  IF NOT LASTBLOCK THEN GOTO 2;
  STOPDMA;
  SETIRQMASK;
  IRQVECTOR (0);
3:ATMHEADER.DATASIZE := ATMBUFPTR;
  WRITELN;
  WRITELN;
4:WRITE ('Name of .ATM-file ? ');
  DESTFILENAME := '';
  INPUTSTRING (59,DESTFILENAME);
  IF USERBREAK THEN EXIT;
  WRITELN;
  WRITELN;
  FOR I := 1 TO LENGTH(DESTFILENAME) DO
    DESTFILENAME[I] := UPCASE(DESTFILENAME[I]);
  IF COPY(DESTFILENAME,LENGTH(DESTFILENAME)-3,4) <> '.ATM' THEN
    DESTFILENAME := DESTFILENAME + '.ATM';
  ASSIGN (TOF,DESTFILENAME);
  RESET (TOF,1);
  IF IORESULT = 0 THEN
  BEGIN
    CLOSE (TOF);
    WRITE ('Filename ',DESTFILENAME,' already exists. Overwrite [Y/N] ? Y',#8);
    WHILE KEYPRESSED DO CH := READKEY;
    REPEAT
      CH := UPCASE(READKEY);
      IF CH=#27 THEN CH := 'N';
      IF CH=#13 THEN CH := 'Y';
    UNTIL (CH='Y') OR (CH='N');
    WRITELN (CH);
    WRITELN;
    IF CH='N' THEN GOTO 4;
  END;
  REWRITE (TOF,1);
  IF IORESULT <> 0 THEN
  BEGIN
    WRITELN ('Access denied or other I/O-error.');
    GOTO 4;
  END;
  BLOCKWRITE (TOF,ATMHEADER,SIZEOF(ATMHEADER));
  BLOCKWRITE (TOF,ATMBUF^,ATMBUFPTR);
  CLOSE (TOF);
  EXIT;
  {if error occurred}
1:STOPDMA;
  SETIRQMASK;
  IRQVECTOR (0);
  ATMBUFPTR := STARTOFBLOCK;
  IF ATMBUFPTR = $0000 THEN EXIT;
  WRITELN;
  WRITE (HEXW(ATMBUFPTR),'h (',ATMBUFPTR,') bytes of data have been ');
  WRITE ('received and verified. Save [Y/N] ? Y',#8);
  WHILE KEYPRESSED DO CH := READKEY;
  REPEAT
    CH := UPCASE(READKEY);
    IF CH=#27 THEN CH := 'N';
    IF CH=#13 THEN CH := 'Y';
  UNTIL (CH='Y') OR (CH='N');
  WRITE (CH);
  IF CH='Y' THEN GOTO 3;
END;

{---[change baudrate]-------------------------------------------------------}
PROCEDURE CHANGEBAUDRATE;
VAR CH:CHAR;
BEGIN
  WRITE ('Use SLOW or FAST tape interface [S/F] ? ');
  IF SPEEDMODE = SCOS THEN WRITE ('S')
                      ELSE WRITE ('F');
  WRITE (#8);
  WHILE KEYPRESSED DO CH := READKEY;
  REPEAT
    CH := UPCASE(READKEY);
    IF (CH=#13) OR (CH=#27) THEN EXIT;
  UNTIL (CH='S') OR (CH='F');
  WRITELN (CH);
  IF CH='S' THEN SPEEDMODE := SCOS
            ELSE SPEEDMODE := FCOS;
END;

{---[main]------------------------------------------------------------------}
LABEL 1;
VAR SELECTION:BYTE;
    PHYSADDR:LONGINT;
    DUMMY:POINTER;
    DUMMYSIZE:LONGINT;
BEGIN
  SPEEDMODE := FCOS;
  CLRSCR;
  TEXTCOLOR (WHITE);
  WRITELN ('-------------------------------------------------------');
  WRITELN (' AtomCom v1.10 (c) Wouter Ras, Delft, Dec 97 - Mar 98.');
  WRITELN ('-------------------------------------------------------');
  WRITELN;
  TEXTCOLOR (LIGHTGRAY);
  WINDOW (1,5,80,25);
  INITBLASTER;
  GETMEM (ATMBUF,SIZEOF(ATMBUFTYPE));
  {allocate memory for dma buffer, make sure it's entirely on 1 page}
  GETMEM (DUMMY,1);
  PHYSADDR := (LONGINT(SEG(DUMMY^)) SHL 4) + LONGINT(OFS(DUMMY^));
  DUMMYSIZE := $10000 - (PHYSADDR AND $FFFF);
  IF DUMMYSIZE >= SIZEOF(DMABUFTYPE) THEN DUMMYSIZE := 0;
  FREEMEM (DUMMY,1);
  GETMEM (DUMMY,DUMMYSIZE);
  GETMEM (DMABUF,SIZEOF(DMABUFTYPE));
1:MAINMENU (SELECTION);
  CASE SELECTION OF 1: BEGIN
                         WRITELN ('Transfer data from PC to ATOM.');
                         WRITELN;
                         LOADSOURCEFILE;
                         IF USERBREAK THEN GOTO 1;
                         PC_TO_ATOM;
                       END;
                    2: BEGIN
                         WRITELN ('Transfer data from ATOM to PC.');
                         WRITELN;
                         ATOM_TO_PC;
                       END;
  END;
  GOTO 1;
END.