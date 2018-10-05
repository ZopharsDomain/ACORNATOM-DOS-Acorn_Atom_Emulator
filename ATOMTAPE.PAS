(***************************************************************************)
(*                                                                         *)
(*    AtomTape v1.1 (c) by Wouter Ras, Delft, November - December 1997     *)
(*    ----------------------------------------------------------------     *)
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

{$r-}
PROGRAM ATOMTAPE;
USES CRT,HEXA;

CONST SILENCE    = $80;
      SILENCEMIN = $7C;
      SILENCEMAX = $84;
      MAXWAVE1   = +12;
      MINWAVE0   = +16;
      MAXWAVE0   = +24;
      VOCHEADER  : ARRAY[$00..$13] OF CHAR = 'Creative Voice File'+#$1a;
TYPE TAPESPEEDTYPE = (SCOS,FCOS);
     BUFTYPE = ARRAY[$0000..$FFF8] OF BYTE;
     ATMHEADERREC = RECORD
                      ATOMNAME     : ARRAY[$00..$0F] OF BYTE;
                      STARTADDRESS : WORD;
                      EXECADDRESS  : WORD;
                      DATASIZE     : WORD;
                    END;

VAR TAPESPEED    : TAPESPEEDTYPE;
    HEADER       : ARRAY[$00..$FF] OF BYTE;
    READBUF      : ^BUFTYPE;
    WRITEBUF     : ^BUFTYPE;
    SOURCEFILE   : STRING;
    DESTFILE     : STRING;
    FROMF        : FILE;
    TOF          :  FILE;
    NOMOREDATA   : BOOLEAN;
    P1           : LONGINT;
    P2           : LONGINT;
    ABSRP        : LONGINT;
    RELRP        : WORD;
    RP           : WORD;
    WP           : WORD;
    HP           : BYTE;
    NR           : WORD;
    LASTBLOCK    : BOOLEAN;
    ATMHEADER    : ATMHEADERREC;
    FIRSTWAVEDOWN: BOOLEAN;


PROCEDURE TERMINATE;
VAR CH:CHAR;
BEGIN
  CLOSE (FROMF);
  CLOSE (TOF);
  ERASE (TOF);
  WRITELN ('Program aborted.');
  WHILE KEYPRESSED DO CH := READKEY;
  HALT;
END;

PROCEDURE GETBYTE (VAR B:BYTE);
BEGIN
  IF NOMOREDATA THEN EXIT;
  B := READBUF^[RP];
  INC (RP);
  IF RP >= NR THEN
  BEGIN
    INC (ABSRP,RP);
    BLOCKREAD (FROMF,READBUF^,SIZEOF(BUFTYPE),NR);
    IF NR=0 THEN NOMOREDATA := TRUE;
    RP := $0000;
  END;
END;

PROCEDURE STOREBYTE (B:BYTE);
VAR I:BYTE;
    W:WORD;
BEGIN
  WRITEBUF^[WP] := B;
  INC (WP);
  IF WP >= SIZEOF(BUFTYPE) THEN
  BEGIN
    BLOCKWRITE (TOF,WRITEBUF^,WP);
    INC (ATMHEADER.DATASIZE,WP);
    WP := $0000;
  END;
END;

PROCEDURE SETSTART;
VAR B:BYTE;
BEGIN
  IF FIRSTWAVEDOWN THEN
  BEGIN
    REPEAT
      GETBYTE (B);
      IF NOMOREDATA THEN EXIT;
    UNTIL B > SILENCEMAX;
    REPEAT
      GETBYTE (B);
      IF NOMOREDATA THEN EXIT;
    UNTIL B < SILENCE;
  END ELSE
  BEGIN
    REPEAT
      GETBYTE (B);
      IF NOMOREDATA THEN EXIT;
    UNTIL B < SILENCEMIN;
    REPEAT
      GETBYTE (B);
      IF NOMOREDATA THEN EXIT;
    UNTIL B > SILENCE;
  END;
END;

PROCEDURE SEEKENDOFWAVE;
VAR B:BYTE;
BEGIN
  IF FIRSTWAVEDOWN THEN
  BEGIN
    REPEAT
      GETBYTE (B);
      IF NOMOREDATA THEN EXIT;
    UNTIL B > SILENCE;
    REPEAT
      GETBYTE (B);
      IF NOMOREDATA THEN EXIT;
    UNTIL B < SILENCE;
  END ELSE
  BEGIN
    REPEAT
      GETBYTE (B);
      IF NOMOREDATA THEN EXIT;
    UNTIL B < SILENCE;
    REPEAT
      GETBYTE (B);
      IF NOMOREDATA THEN EXIT;
    UNTIL B > SILENCE;
  END;
END;

PROCEDURE READONEBYTEFROMVOC (FIRSTWAVEDONE:BOOLEAN; VAR B:BYTE);
VAR DATABITS:ARRAY[0..9] OF BYTE;
    S:STRING[16];
    I:BYTE;
    A:BYTE;
BEGIN
  I := 0;
  DATABITS[0] := 0;
  S := '';
  IF TAPESPEED = SCOS THEN
  BEGIN
    IF FIRSTWAVEDONE THEN S := '00';
  END ELSE
  BEGIN
    IF FIRSTWAVEDONE THEN I := 1;
  END;
  WHILE I <= 9 DO
  BEGIN
    P1 := P2;
    SEEKENDOFWAVE;
    IF NOMOREDATA THEN EXIT;
    P2 := ABSRP + LONGINT(RP);
    IF P2-P1 <= MAXWAVE1 THEN
    BEGIN
      S := S + '1';
    END ELSE
      IF P2-P1 >= MINWAVE0 THEN
      BEGIN
        S := S + '00';
      END ELSE
      BEGIN
        GOTOXY (1,WHEREY);
        WRITELN ('Error: Misformed wave pattern at position ',HEXL(P1),'h.');
        TERMINATE;
      END;
    IF ((TAPESPEED = FCOS) AND (S='00')) OR
       ((TAPESPEED = SCOS) AND (S='00000000')) THEN
    BEGIN
      DATABITS[I] := 0;
      INC (I);
      S := '';
    END ELSE
      IF ((TAPESPEED = FCOS) AND (S='11')) OR
         ((TAPESPEED = SCOS) AND (S='11111111')) THEN
      BEGIN
        DATABITS[I] := 1;
        INC (I);
        S := '';
      END;
    IF ((TAPESPEED = FCOS) AND (LENGTH(S) > 2)) OR
       ((TAPESPEED = SCOS) AND (LENGTH(S) > 8)) THEN
    BEGIN
      GOTOXY (1,WHEREY);
      WRITELN ('Error: Misformed wave pattern at position ',HEXL(P1),'h.');
      TERMINATE;
    END;
  END;
  P1 := P2;
  SEEKENDOFWAVE; {---stopbit always has one extra wave---}
  IF NOMOREDATA THEN EXIT;
  P2 := ABSRP + LONGINT(RP);
  IF DATABITS[0] <> $00 THEN
  BEGIN
    GOTOXY (1,WHEREY);
    WRITELN ('Error: No startbit (0) found at position ',HEXL(P1),'h.');
    TERMINATE;
  END;
  IF DATABITS[9] <> $01 THEN
  BEGIN
    GOTOXY (1,WHEREY);
    WRITELN ('Error: No stopbit (1) found at position ',HEXL(P1),'h.');
    TERMINATE;
  END;
  B := $00;
  A := $01;
  FOR I := 1 TO 8 DO
  BEGIN
    IF DATABITS[I] <> $00 THEN B := B OR A;
    A := (A SHL 1) AND $FF;
  END;
  IF KEYPRESSED THEN
  BEGIN
    GOTOXY (1,WHEREY);
    CLREOL;
    WRITELN ('User break.');
    TERMINATE;
  END;
END;

PROCEDURE INPUTSTRING (LENGTE:BYTE;VAR S:STRING);
LABEL 1;
VAR CH,DH:CHAR;
    N,P:BYTE;
    XC,YC:BYTE;
    T:STRING;
BEGIN
  T := '';
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
                     WRITELN;
                     WRITELN;
                     WRITELN ('User break.');
                     HALT;
                   END;
  UNTIL (CH=#13);
  WHILE S[LENGTH(S)] = '_' DO DELETE (S,LENGTH(S),1);
  IF S='' THEN GOTO 1;
  GOTOXY (XC,YC);
  WRITE (S);
  CLREOL;
END;

PROCEDURE CREATETEMPFILE;
LABEL 1;
VAR TOF:FILE;
    BLOCKSIZE:LONGINT;
    BLOCK01POS:LONGINT;
    TOTALSIZE:LONGINT;
    AANTAL:WORD;
BEGIN
  WRITE ('File consists of more than one datablocks. Restructuring file...');
  SEEK (FROMF,0);
  ASSIGN (TOF,'$ATMTEMP.TMP');
  REWRITE (TOF,1);
  {---header---}
  BLOCKREAD (FROMF,READBUF^,$1A,NR);
  BLOCKWRITE (TOF,READBUF^,$1A);
  {---data (including block 8)---}
  BLOCKREAD (FROMF,READBUF^,$04,NR);
  WHILE (READBUF^[$00] > $02) AND (READBUF^[$00] <> $08) DO
  BEGIN
    BLOCKSIZE := LONGINT(READBUF^[$01]) +
                 (LONGINT(READBUF^[$02]) SHL 8) +
                 (LONGINT(READBUF^[$03]) SHL 16);
    SEEK (FROMF,FILEPOS(FROMF)+BLOCKSIZE);
    BLOCKREAD (FROMF,READBUF^,$04,NR);
  END;
  IF READBUF^[$00] = $08 THEN
  BEGIN
    BLOCKWRITE (TOF,READBUF^,$04);
    BLOCKSIZE := LONGINT(READBUF^[$01]) +
                 (LONGINT(READBUF^[$02]) SHL 8) +
                 (LONGINT(READBUF^[$03]) SHL 16);
    BLOCKREAD (FROMF,READBUF^,BLOCKSIZE,NR);
    BLOCKWRITE (TOF,READBUF^,NR);
    BLOCKREAD (FROMF,READBUF^,$04,NR);
  END;
  IF READBUF^[$00] = $01 THEN
  BEGIN
    BLOCK01POS := FILESIZE(TOF);
    TOTALSIZE := $02;
    BLOCKWRITE (TOF,READBUF^,$04);
    BLOCKSIZE := LONGINT(READBUF^[$01]) +
                 (LONGINT(READBUF^[$02]) SHL 8) +
                 (LONGINT(READBUF^[$03]) SHL 16);
    BLOCKREAD (FROMF,READBUF^,$02,NR);
    BLOCKWRITE (TOF,READBUF^,$02);
    DEC (BLOCKSIZE,$02);
  END ELSE
  BEGIN
    CLOSE (FROMF);
    CLOSE (TOF);
    ERASE (TOF);
    WRITELN ('Error: No information about samplerate etc. encountered.');
    HALT;
  END;
  {---rest of data; block 8 ignored---}
1:WHILE BLOCKSIZE > 0 DO
  BEGIN
    AANTAL := SIZEOF(BUFTYPE);
    IF AANTAL > BLOCKSIZE THEN AANTAL := BLOCKSIZE;
    INC (TOTALSIZE,AANTAL);
    BLOCKREAD (FROMF,READBUF^,AANTAL,NR);
    BLOCKWRITE (TOF,READBUF^,NR);
    DEC (BLOCKSIZE,NR);
  END;
  BLOCKREAD (FROMF,READBUF^,$04,NR);
  IF READBUF^[$00] = $01 THEN
  BEGIN
    BLOCKSIZE := LONGINT(READBUF^[$01]) +
                 (LONGINT(READBUF^[$02]) SHL 8) +
                 (LONGINT(READBUF^[$03]) SHL 16);
    SEEK (FROMF,FILEPOS(FROMF)+$02);
    DEC (BLOCKSIZE,$02);
  END;
  IF READBUF^[$00] = $02 THEN
  BEGIN
    BLOCKSIZE := LONGINT(READBUF^[$01]) +
                 (LONGINT(READBUF^[$02]) SHL 8) +
                 (LONGINT(READBUF^[$03]) SHL 16);
  END;
  IF READBUF^[$00] <> $00 THEN GOTO 1;
  BLOCKWRITE (TOF,READBUF^,$01);
  SEEK (TOF,SUCC(BLOCK01POS));
  BLOCKWRITE (TOF,TOTALSIZE,$03);
  CLOSE (FROMF);
  CLOSE (TOF);
  ERASE (FROMF);
  RENAME (TOF,SOURCEFILE);
  WRITELN;
  ASSIGN (FROMF,SOURCEFILE);
  RESET (FROMF,1);
END;

{===[main]==================================================================}
LABEL 1,2,3;
VAR CH           : CHAR;
    DH           : CHAR;
    W            : WORD;
    B            : BYTE;
    I            : BYTE;
    CHKSUM       : BYTE;
    EERSTE       : BOOLEAN;
    NUMBYTES     : WORD;
    SR           : WORD;
    BLOCKSIZE    : LONGINT;
BEGIN
  GETMEM (READBUF,SIZEOF(BUFTYPE));
  GETMEM (WRITEBUF,SIZEOF(BUFTYPE));
  CLRSCR;
  WRITELN ('AtomTape v1.1 (c) Wouter Ras, Delft, November-December 1997');
  WRITELN;
  WRITELN;
  WRITE ('Name of VOC-file (without extension) ? ');
  INPUTSTRING (30,SOURCEFILE);
  FOR I := 1 TO LENGTH(SOURCEFILE) DO SOURCEFILE[I] := UPCASE(SOURCEFILE[I]);
  DESTFILE := SOURCEFILE + '.ATM';
  SOURCEFILE := SOURCEFILE + '.VOC';
  WRITELN;
  WRITELN;
  ASSIGN (FROMF,SOURCEFILE);
  {$i-}
  RESET (FROMF,1);
  {$i+}
  IF IORESULT <> 0 THEN
  BEGIN
    WRITELN ('Source file (',SOURCEFILE,') not found.');
    HALT;
  END;
  WRITE ('Is it a 300 bps (slow) or 1200 bps (fast) file [S/F] ? F',#8);
  WHILE KEYPRESSED DO CH := READKEY;
  REPEAT
    CH := UPCASE(READKEY);
    IF CH=#0 THEN DH := READKEY;
    IF CH=#27 THEN BEGIN
                     WRITELN;
                     WRITELN;
                     WRITELN ('User break.');
                     CLOSE (FROMF);
                     HALT;
                   END;
    IF CH=#13 THEN CH := 'F';
  UNTIL (CH='F') OR (CH='S');
  WRITELN (CH);
  WRITELN;
  WRITELN;
  IF CH='S' THEN TAPESPEED := SCOS
            ELSE TAPESPEED := FCOS;
  FOR I := $00 TO $0F DO ATMHEADER.ATOMNAME[I] := $00;
  ATMHEADER.DATASIZE := 0;
3:BLOCKREAD (FROMF,READBUF^,SIZEOF(BUFTYPE),NR);
  FOR I := $00 TO $13 DO
  BEGIN
    IF READBUF^[I] <> ORD(VOCHEADER[I]) THEN
    BEGIN
      WRITELN ('This is not a valid VOC-file.');
      CLOSE (FROMF);
      HALT;
    END;
  END;
  RP := $001A;
  WHILE (READBUF^[RP] <> $01) AND (READBUF^[RP] <> $08) DO
  BEGIN
    IF READBUF^[RP] = $02 THEN
    BEGIN
      WRITELN ('No information about samplerate etc. encountered.');
      CLOSE (FROMF);
      HALT;
    END;
    IF (READBUF^[RP] >= $03) AND (READBUF^[RP] <=07) THEN
    BEGIN
      BLOCKSIZE := LONGINT(READBUF^[RP+$01]) +
                   (LONGINT(READBUF^[RP+$02]) SHL 8) +
                   (LONGINT(READBUF^[RP+$03]) SHL 16);
      INC (RP,BLOCKSIZE+$04);
    END;
  END;
  IF READBUF^[RP] = $08 THEN
  BEGIN
    SR := READBUF^[RP+$04] + SWAP(WORD(READBUF^[RP+$05]));
    IF (SR < $D2A7-$80) OR (SR > $D2A7+$80) THEN
    BEGIN
      WRITELN ('Wrong samplerate. It should be 22050 Hz.');
      CLOSE (FROMF);
      HALT;
    END;
    IF (READBUF^[RP+$06] <> $00) OR (READBUF^[RP+$07] <> $00) THEN
    BEGIN
      WRITELN ('File must be 8-bits sample mono recorded.');
      CLOSE (FROMF);
      HALT;
    END;
    RP := $0022;
    BLOCKSIZE := LONGINT(READBUF^[RP+$01]) +
                 (LONGINT(READBUF^[RP+$02]) SHL 8) +
                 (LONGINT(READBUF^[RP+$03]) SHL 16);
    IF BLOCKSIZE <> FILESIZE(FROMF)-(RP+$04)-$01 THEN
    BEGIN
      CREATETEMPFILE;
      GOTO 3;
    END;
    RP := $0028;
  END ELSE
  BEGIN
    IF READBUF^[RP] = $01 THEN
    BEGIN
      BLOCKSIZE := LONGINT(READBUF^[RP+$01]) +
                   (LONGINT(READBUF^[RP+$02]) SHL 8) +
                   (LONGINT(READBUF^[RP+$03]) SHL 16);
      IF BLOCKSIZE <> FILESIZE(FROMF)-(RP+$04)-$01 THEN
      BEGIN
        CREATETEMPFILE;
        GOTO 3;
      END;
      IF (READBUF^[RP+$04] < $D2) OR (READBUF^[RP+$04] > $D3) THEN
      BEGIN
        WRITELN ('Wrong samplerate. It should be 22050 Hz.');
        CLOSE (FROMF);
        HALT;
      END;
      IF READBUF^[RP+$05] <> $00 THEN
      BEGIN
        WRITELN ('File must be 8-bits sample mono recorded.');
        CLOSE (FROMF);
        HALT;
      END;
      RP := $0020;
    END ELSE
    BEGIN
      WRITELN ('Unrecognised VOC-block. Only blocktypes 1 and 8 are allowed.');
      CLOSE (FROMF);
      HALT;
    END;
  END;
  ABSRP := RP;
  NOMOREDATA := FALSE;
  ASSIGN (TOF,DESTFILE);
  REWRITE (TOF,1);
  BLOCKWRITE (TOF,ATMHEADER,SIZEOF(ATMHEADER));
  WP := $0000;
  WRITELN ('Analyzing VOC-file:');
  WRITELN;
  WRITELN ('Atom filename   Strt End  Exec  Nr');
  WRITELN ('--------------- ---- ---- ----  --');
2:FIRSTWAVEDOWN := TRUE;
  {---searching for header---}
  WRITE ('Searching header...');
  SETSTART;
  IF NOMOREDATA THEN GOTO 1;
  P2 := ABSRP + LONGINT(RP);
  REPEAT
    P1 := P2;
    SEEKENDOFWAVE;
    IF NOMOREDATA THEN GOTO 1;
    P2 := ABSRP + LONGINT(RP);
  UNTIL (P2-P1 > MAXWAVE1) AND (P2-P1 <= MAXWAVE0);
  IF P2-P1 < MINWAVE0 THEN {swap wavestart}
  BEGIN
    FIRSTWAVEDOWN := FALSE;
    SEEKENDOFWAVE;
    IF NOMOREDATA THEN GOTO 1;
    P2 := ABSRP + LONGINT(RP);
  END;
  {---read header---}
  GOTOXY (1,WHEREY);
  WRITE ('Reading header...');
  CLREOL;
  HP := 0;
  EERSTE := TRUE;
  CHKSUM := 0;
  REPEAT
    INC(MEM[$B800:2*80*25]);
    READONEBYTEFROMVOC (EERSTE,B);
    EERSTE := FALSE;
    IF NOMOREDATA THEN GOTO 1;
    HEADER[HP] := B;
    CHKSUM := LO(CHKSUM + B);
    INC (HP);
  UNTIL (HP >= $0D) AND (HEADER[HP-$09] = $0D);
  GOTOXY (1,WHEREY);
  IF (HEADER[$00] <> ORD('*')) OR (HEADER[$01] <> ORD('*')) OR
     (HEADER[$02] <> ORD('*')) OR (HEADER[$03] <> ORD('*')) THEN
  BEGIN
    WRITELN ('Error: Blockheader corrupted.');
    TERMINATE;
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
  WRITE ('Searching datablock...');
  REPEAT
    P1 := P2;
    SEEKENDOFWAVE;
    IF NOMOREDATA THEN EXIT;
    P2 := ABSRP + LONGINT(RP);
  UNTIL P2-P1 <= MAXWAVE1;
  REPEAT
    P1 := P2;
    SEEKENDOFWAVE;
    IF NOMOREDATA THEN EXIT;
    P2 := ABSRP + LONGINT(RP);
  UNTIL (P2-P1 > MAXWAVE1) AND (P2-P1 <= MAXWAVE0);
  {---read datablock---}
  GOTOXY (1,WHEREY);
  WRITE ('Reading datablock...');
  CLREOL;
  EERSTE := TRUE;
  FOR W := 1 TO NUMBYTES DO
  BEGIN
    INC(MEM[$B800:2*80*25]);
    READONEBYTEFROMVOC (EERSTE,B);
    EERSTE := FALSE;
    IF NOMOREDATA THEN GOTO 1;
    STOREBYTE (B);
    CHKSUM := LO(CHKSUM + B);
  END;
  READONEBYTEFROMVOC (FALSE,B); {---checksum---}
  GOTOXY (1,WHEREY);
  CLREOL;
  IF B <> CHKSUM THEN
  BEGIN
    WRITELN ('Checksum error: ',HEX(CHKSUM),'h should be ',HEX(B),'h.');
    TERMINATE;
  END;
  IF NOT LASTBLOCK THEN GOTO 2;
1:BLOCKWRITE (TOF,WRITEBUF^,WP);
  INC (ATMHEADER.DATASIZE,WP);
  CLOSE (FROMF);
  CLOSE (TOF);
  RESET (TOF,1);
  BLOCKWRITE (TOF,ATMHEADER,SIZEOF(ATMHEADER));
  CLOSE (TOF);
  WHILE KEYPRESSED DO CH := READKEY;
  IF NOT LASTBLOCK THEN
  BEGIN
    GOTOXY (1,WHEREY);
    WRITELN ('Alert: File might be incomplete.');
  END ELSE
  BEGIN
    WRITELN ('Ready.');
  END;
END.