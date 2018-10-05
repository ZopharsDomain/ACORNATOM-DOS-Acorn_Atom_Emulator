(***************************************************************************)
(*                                                                         *)
(* Acorn Atom Emulator v1.33 (c) by Wouter Ras, Delft, Oct 1997 - May 1999 *)
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
(* Please report any problems, questions, comments to me at one or both of *)
(* these addresses: avio@casema.net                                        *)
(*                  wouterras@hotmail.com                                  *)
(*                                                                         *)
(* The latest version of the emulator can be downloaded from my Atom-page: *)
(* http://www.casema.net/~avio/atom.htm                                    *)
(*                                                                         *)
(***************************************************************************)

{$g+,f-,i-,r-,s-,m 16384,273500,273500}
PROGRAM ACORN_ATOM;
USES DOS,ATOMROM,FDC8271,LEENDERT;
CONST FOUTBUFSIZE  = $1000;
      MAXAANTFILES = 400;
TYPE STR2 = STRING[2];
     STR4 = STRING[4];
     STR8 = STRING[8];
     FILELISTTYPE  = ARRAY[0..PRED(MAXAANTFILES)] OF STR8;
     ATMFILEREC    = RECORD
                       ATMNAME   : ARRAY[$00..$0F] OF CHAR;
                       STARTADRS : WORD;
                       EXECADRS  : WORD;
                       DATASIZE  : WORD;
                     END;
     ATMFILETYPE   = ARRAY[0..PRED(MAXAANTFILES)] OF ATMFILEREC;
     FINBUFTYPE    = ARRAY[$0000..$FFF8] OF BYTE;
     FOUTBUFTYPE   = ARRAY[$0000..PRED(FOUTBUFSIZE)] OF BYTE;
     TEMPMOUSETYPE = RECORD
                       B_BFE0    : BYTE;
                       B_BFE1    : BYTE;
                       B_MOUSENR : BYTE;
                       MOUSEX    : WORD;
                       MOUSEY    : WORD;
                     END;

CONST NMI_VECTOR    = $FFFA;
      RES_VECTOR    = $FFFC; {reset}
      IRQ_VECTOR    = $FFFE;
      BRK_VECTOR    = $FFFE;
      STACKBASE     = $0100;
      CYCLESFLYBACK = +2040; {number of cycles during flyback}
      COUNTER       = $BFF4; {WORD: counter for checking F9, F12 etc.}
      IRQ_NMI       = $BFF6; {BYTE: NMI or IRQ request, see also FDC8271}
      INSTRCYCLES   = $BFF7; {BYTE: number of cycles for an instruction}
      PCCYCLES      = $BFF8; {WORD: number of cycles that the PC needs to execute an instruction}
      AANTCYCLES    = $BFFA; {WORD: keep track of the cycles}
      WACHTSCHULD   = $BFFC; {WORD: built-up debt, e.g. because of screenupdates}
      SCHAKELBYTE   = $BFFF; {BYTE: switchbyte for EPROM at A000h}
      LOADVEC       = $020C;
      SAVEVEC       = $020E;
      GETBYTEVEC    = $0214;
      PUTBYTEVEC    = $0216;
      FINDVEC       = $0218;
      FLIPFLOP      = $BF7F;
      STR8GROOTTE   = SIZEOF(STR8);
      ATMRECGROOTTE = SIZEOF(ATMFILEREC);
      HEXSTR        : ARRAY[$00..$0F] OF CHAR = '0123456789ABCDEF';
VAR ATOMMEM1        : POINTER;
    ATOMMEM2        : POINTER;
    ATOMMEM3        : POINTER;
    BOXNAMES        : ARRAY[0..15,0..15] OF CHAR;
    DISKIMAGES      : FILELISTTYPE;
    AANTALDISKIMAGES: INTEGER; {number of disk images}
    TAPEIMAGES      : FILELISTTYPE;
    AANTALTAPEIMAGES: INTEGER; {number of tape images}
    IMPFILES        : ATMFILETYPE;
    AANTALIMPFILES  : INTEGER; {number of importable files}
    ATOMFILES       : ATMFILETYPE;
    AANTALATOMFILES : INTEGER; {number of atom files in an image}
    ATOMMEMSEG      : WORD;
    IOPORT          : WORD; {soundblaster base i/o port}
    CHARDATA        : ARRAY[$00..$BF,$00..$0F] OF BYTE;
    MONOGRAPHTABLE  : ARRAY[$00..$FF,$00..$03] OF WORD;
    GREYGRAPHTABLE  : ARRAY[$00..$FF,$00..$03] OF WORD;
    COLORGRAPHTABLE : ARRAY[$00..$FF,$00..$03] OF WORD;
    TAPEIMAGENAME   : STRING[8];
    EXTROMFILE      : STRING[12];
    FOUTNAME        : STRING[16];
    IMAGEFOUTNAME   : STRING[8];
    CATSEARCH       : ARRAY[0..15] OF CHAR;
    FINBUF          : ^FINBUFTYPE;
    FINBUFPTR       : WORD;
    FINBUFOFS       : WORD;
    FINBUFSEG       : WORD;
    FINSIZE         : WORD;
    FOUTBUF         : ^FOUTBUFTYPE;
    FOUTBUFPTR      : WORD;
    FOUTBUFOFS      : WORD;
    FOUTBUFSEG      : WORD;
    FOUTOPEN        : BYTE;
    BMPHEADER       : ARRAY[$0000..$0075] OF BYTE;
    MOUSEBACKGROUND : ARRAY[0..7,0..7] OF WORD;
    MOUSEPOINTER    : ARRAY[0..7,0..7] OF WORD;
    TEMPMOUSEDAT    : TEMPMOUSETYPE;

{===========================================================================}
{A number of variables will be declared here as procedures. This was to only}
{way that I could think of to have  them reside in the CSEG and keeping them}
{global.  During  emulation the DS register  is pointing to  the Atom memory}
{segment, the ES register  is A000h, i.e. the  video bank; Reading/writing a}
{variable using the CS: prefix  takes much less time than swapping the DS or}
{ES registers all the time.                                                 }
{Every procedure with this purpose has the ASSEMBLER directive, meaning that}
{no stackframe is generated.  The RETN instruction (C3h) is generated at the}
{end of the proc. automatically and takes one byte (sometimes used as data).}
{===========================================================================}

{---[toets (english: key)]--------------------------------------------------}
PROCEDURE TOETS; ASSEMBLER;
ASM;
               DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
               DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
               DW    0
END;

{---[filenamebuf]-----------------------------------------------------------}
PROCEDURE FILENAMEBUF; ASSEMBLER;
ASM;
               DD    0,0,0,0
END;

{---[widertable]------------------------------------------------------------}
PROCEDURE WIDERTABLE; ASSEMBLER;
ASM;
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
END;

{---[wider1atable]----------------------------------------------------------}
PROCEDURE WIDER1aTABLE; ASSEMBLER;
ASM;
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
  DD    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0
END;

{---[opcodes (used for disassembling)]--------------------------------------}
PROCEDURE OPCODES; ASSEMBLER;
{ first digit  = mnemonic                             }
{ second digit = 1 Accumulator  ³ 8 Absolute, Y       }
{                2 Immediate    ³ 9 Implied           }
{                3 Zero Page    ³10 Relative          }
{                4 Zero Page, X ³11 (Indirect, X)     }
{                5 Zero Page, Y ³12 (Indirect), Y     }
{                6 Absolute     ³13 Absolute Indirect }
{                7 Absolute, X  ³14 (Indirect)        }
{                               ³15 (Abs.Indirect, X) }
ASM;
               DB    11, 9, 35,11, 70, 9, 34, 9, 64, 3, 35, 3,  3, 3, 34, 9
               DB    37, 9, 35, 2,  3, 1, 34, 9, 64, 6, 35, 6,  3, 6, 34, 9
{10}           DB    10,10, 35,12, 35,14, 34, 9, 63, 3, 35, 4,  3, 4, 34, 9
               DB    14, 9, 35, 8, 25, 1, 66, 9, 63, 6, 35, 7,  3, 7, 34, 9
{20}           DB    29, 6,  2,11, 34, 3, 34, 9,  7, 3,  2, 3, 40, 3, 34, 9
               DB    39, 9,  2, 2, 40, 1, 34, 9,  7, 6,  2, 6, 40, 6, 34, 9
{30}           DB     8,10,  2,12,  2,14, 34, 9,  7, 4,  2, 4, 40, 4, 34, 9
               DB    45, 9,  2, 8, 21, 1, 67, 9,  7, 7,  2, 7, 40, 7, 34, 9
{40}           DB    42, 9, 24,11, 34, 3, 34, 9, 34, 3, 24, 3, 33, 3, 34, 9
               DB    36, 9, 24, 2, 33, 1, 34, 9, 28, 6, 24, 6, 33, 6, 34, 9
{50}           DB    12,10, 24,12, 24,14, 34, 9, 34, 3, 24, 4, 33, 4, 34, 9
               DB    16, 9, 24, 8, 59, 9, 34, 9, 34, 6, 24, 7, 33, 7, 34, 9
{60}           DB    43, 9,  1,11, 34, 3, 34, 9, 62, 3,  1, 3, 41, 3, 34, 9
               DB    38, 9,  1, 2, 41, 1, 34, 9, 28,13,  1, 6, 41, 6, 34, 9
{70}           DB    13,10,  1,12,  1,14, 34, 9, 62, 4,  1, 4, 41, 4, 34, 9
               DB    47, 9,  1, 8, 61, 9, 34, 9, 28,15,  1, 7, 41, 7, 34, 9
{80}           DB    57,10, 48,11, 34, 3, 34, 9, 50, 3, 48, 3, 49, 3, 34, 9
               DB    23, 9,  7, 2, 54, 9, 34, 9, 50, 6, 48, 6, 49, 6, 34, 9
{90}           DB     4,10, 48,12, 48,14, 34, 9, 50, 4, 48, 4, 49, 5, 34, 9
               DB    56, 9, 48, 8, 55, 9, 68, 9, 62, 6, 48, 7, 62, 7, 34, 9
{A0}           DB    32, 2, 30,11, 31, 2, 34, 9, 32, 3, 30, 3, 31, 3, 34, 9
               DB    52, 9, 30, 2, 51, 9, 34, 9, 32, 6, 30, 6, 31, 6, 34, 9
{B0}           DB     5,10, 30,12, 30,14, 34, 9, 32, 4, 30, 4, 31, 5, 34, 9
               DB    17, 9, 30, 8, 53, 9, 69, 9, 32, 7, 30, 7, 31, 8, 34, 9
{C0}           DB    20, 2, 18,11, 34, 3, 34, 9, 20, 3, 18, 3, 21, 3, 34, 9
               DB    27, 9, 18, 2, 22, 9, 34, 9, 20, 6, 18, 6, 21, 6, 34, 9
{D0}           DB     9,10, 18,12, 18,14, 34, 9, 34, 3, 18, 4, 21, 4, 34, 9
               DB    15, 9, 18, 8, 58, 9, 34, 9, 34, 6, 18, 7, 21, 7, 34, 9
{E0}           DB    19, 2, 44,11, 34, 3, 34, 9, 19, 3, 44, 3, 25, 3, 34, 9
               DB    26, 9, 44, 2, 34, 9, 65, 9, 19, 6, 44, 6, 25, 6, 34, 9
{F0}           DB     6,10, 44,12, 44,14, 34, 9, 34, 3, 44, 4, 25, 4, 34, 9
               DB    46, 9, 44, 8, 60, 9, 34, 9, 29,15, 44, 7, 25, 7, 34, 9
END;

{---[mnemonics]-------------------------------------------------------------}
PROCEDURE MNEMONICS; ASSEMBLER;
ASM;
               DB    '???','ADC','AND','ASL','BCC','BCS','BEQ','BIT','BMI','BNE'{ 0}
               DB    'BPL','BRK','BVC','BVS','CLC','CLD','CLI','CLV','CMP','CPX'{10}
               DB    'CPY','DEC','DEX','DEY','EOR','INC','INX','INY','JMP','JSR'{20}
               DB    'LDA','LDX','LDY','LSR','NOP','ORA','PHA','PHP','PLA','PLP'{30}
               DB    'ROL','ROR','RTI','RTS','SBC','SEC','SED','SEI','STA','STX'{40}
               DB    'STY','TAX','TAY','TSX','TXA','TXS','TYA','BRA','PHX','PHY'{50}
               DB    'PLX','PLY','STZ','TRB','TSB','SWA','TAS','TSA','TXY','TYX'{60}
               DB    'COP'                                                      {70}
END;

{---[decnum]----------------------------------------------------------------}
PROCEDURE DECNUM; ASSEMBLER;
ASM;
               DB    $00,$00,$00,$00,$00,$00
END;

{---[characters (need to be ROLled left 1 bit)]-----------------------------}
PROCEDURE CHARACTERS; ASSEMBLER;
ASM;
               DB    $0E,$11,$01,$0D,$15,$15,$0E {@}
               DB    $04,$0A,$11,$11,$1F,$11,$11 {A}
               DB    $1E,$09,$09,$0E,$09,$09,$1E {B}
               DB    $0E,$11,$10,$10,$10,$11,$0E {C}
               DB    $1E,$09,$09,$09,$09,$09,$1E {D}
               DB    $1F,$10,$10,$1C,$10,$10,$1F {E}
               DB    $1F,$10,$10,$1E,$10,$10,$10 {F}
               DB    $0F,$10,$10,$13,$11,$11,$0F {G}
               DB    $11,$11,$11,$1F,$11,$11,$11 {H}
               DB    $0E,$04,$04,$04,$04,$04,$0E {I}
               DB    $01,$01,$01,$01,$11,$11,$0E {J}
               DB    $11,$12,$14,$18,$14,$12,$11 {K}
               DB    $10,$10,$10,$10,$10,$10,$1F {L}
               DB    $11,$1B,$15,$15,$11,$11,$11 {M}
               DB    $11,$19,$15,$13,$11,$11,$11 {N}
               DB    $1F,$11,$11,$11,$11,$11,$1F {O}

               DB    $1E,$11,$11,$1E,$10,$10,$10 {P}
               DB    $0E,$11,$11,$11,$15,$12,$0D {Q}
               DB    $1E,$11,$11,$1E,$14,$12,$11 {R}
               DB    $0E,$11,$08,$04,$02,$11,$0E {S}
               DB    $1F,$04,$04,$04,$04,$04,$04 {T}
               DB    $11,$11,$11,$11,$11,$11,$0E {U}
               DB    $11,$11,$11,$11,$0A,$0A,$04 {V}
               DB    $11,$11,$11,$15,$15,$1B,$11 {W}
               DB    $11,$11,$0A,$04,$0A,$11,$11 {X}
               DB    $11,$11,$0A,$04,$04,$04,$04 {Y}
               DB    $1F,$01,$02,$04,$08,$10,$1F {Z}
               DB    $0E,$08,$08,$08,$08,$08,$0E {[}
               DB    $10,$10,$08,$04,$02,$01,$01 {\}
               DB    $0E,$02,$02,$02,$02,$02,$0E {]}
               DB    $04,$0E,$15,$04,$04,$04,$04 {^}
               DB    $00,$04,$08,$1F,$08,$04,$00 {<-}

               DB    $00,$00,$00,$00,$00,$00,$00 {space}
               DB    $04,$04,$04,$04,$04,$00,$04 {!}
               DB    $0A,$0A,$00,$00,$00,$00,$00 {"}
               DB    $0A,$0A,$1B,$00,$1B,$0A,$0A {#}
               DB    $04,$0F,$10,$0E,$01,$1E,$04 {"$"}
               DB    $19,$19,$02,$04,$08,$13,$13 {%}
               DB    $08,$14,$14,$08,$15,$12,$0D {&}
               DB    $06,$06,$06,$00,$00,$00,$00 {'}
               DB    $02,$04,$08,$08,$08,$04,$02 {(}
               DB    $08,$04,$02,$02,$02,$04,$08 {)}
               DB    $00,$04,$0E,$1F,$0E,$04,$00 {*}
               DB    $00,$04,$04,$1F,$04,$04,$00 {+}
               DB    $00,$00,$00,$06,$06,$02,$04 {,}
               DB    $00,$00,$00,$1F,$00,$00,$00 {-}
               DB    $00,$00,$00,$00,$00,$06,$06 {.}
               DB    $01,$01,$02,$04,$08,$10,$10 {/}

               DB    $0C,$12,$12,$12,$12,$12,$0C {0}
               DB    $04,$0C,$04,$04,$04,$04,$0E {1}
               DB    $0E,$11,$01,$0E,$10,$10,$1F {2}
               DB    $0E,$11,$01,$06,$01,$11,$0E {3}
               DB    $02,$06,$0A,$1F,$02,$02,$02 {4}
               DB    $1F,$10,$1E,$01,$01,$11,$0E {5}
               DB    $0E,$10,$10,$1E,$11,$11,$0E {6}
               DB    $1F,$01,$02,$04,$08,$10,$10 {7}
               DB    $0E,$11,$11,$0E,$11,$11,$0E {8}
               DB    $0E,$11,$11,$0F,$01,$01,$0E {9}
               DB    $00,$06,$06,$00,$06,$06,$00 {:}
               DB    $06,$06,$00,$06,$06,$02,$04 {;}
               DB    $02,$04,$08,$10,$08,$04,$02 {<}
               DB    $00,$00,$1F,$00,$1F,$00,$00 {=}
               DB    $10,$08,$04,$02,$04,$08,$10 {>}
               DB    $0C,$12,$02,$04,$04,$00,$04 {?}
END;

{---[mousecursors]----------------------------------------------------------}
PROCEDURE MOUSECURSORS; ASSEMBLER;
ASM;
{00h}          DB    11111111b
               DB    10000010b
               DB    10000100b
               DB    10000100b
               DB    10000010b
               DB    10110001b
               DB    11001010b
               DB    10000100b

{01h}          DB    11111100b
               DB    11111000b
               DB    11110000b
               DB    11111000b
               DB    11011100b
               DB    10001110b
               DB    00000111b
               DB    00000010b

{02h}          DB    00111100b
               DB    01010010b
               DB    10010001b
               DB    10010001b
               DB    10011101b
               DB    10000001b
               DB    01000010b
               DB    00111100b

{03h}          DB    11110000b
               DB    11000000b
               DB    10100000b
               DB    10010000b
               DB    00001000b
               DB    00000100b
               DB    00000000b
               DB    00000000b

{04h}          DB    00010000b
               DB    00101000b
               DB    01000100b
               DB    11000110b
               DB    01000100b
               DB    01000100b
               DB    01000100b
               DB    01111100b

{05h}          DB    01111100b
               DB    01000100b
               DB    01000100b
               DB    01000100b
               DB    11000110b
               DB    01000100b
               DB    00101000b
               DB    00010000b

{06h}          DB    00001000b
               DB    11111100b
               DB    10000010b
               DB    10000001b
               DB    10000010b
               DB    11111100b
               DB    00001000b
               DB    00000000b

{07h}          DB    00010000b
               DB    00111111b
               DB    01000001b
               DB    10000001b
               DB    01000001b
               DB    00111111b
               DB    00010000b
               DB    00000000b

{08h}          DB    00111100b
               DB    01000110b
               DB    10001101b
               DB    10001101b
               DB    10011001b
               DB    10011001b
               DB    01110010b
               DB    00111100b

{09h}          DB    00111000b
               DB    01000100b
               DB    01010100b
               DB    01110100b
               DB    00101000b
               DB    00111000b
               DB    00101000b
               DB    00111000b

{0Ah}          DB    01111100b
               DB    01000100b
               DB    01101100b
               DB    00101000b
               DB    00101000b
               DB    01101100b
               DB    01000100b
               DB    01111100b

{0Bh}          DB    00111000b
               DB    00101000b
               DB    11101110b
               DB    10000010b
               DB    11101110b
               DB    00101000b
               DB    00111000b
               DB    00000000b

{0Ch}          DB    01000000b
               DB    10100000b
               DB    10100000b
               DB    10111110b
               DB    10101011b
               DB    10000001b
               DB    11111111b
               DB    01111110b

{0Dh}          DB    01111110b
               DB    11111111b
               DB    10000001b
               DB    10101011b
               DB    10111110b
               DB    10100000b
               DB    10100000b
               DB    01000000b

{0Eh}          DB    01111110b
               DB    11000001b
               DB    11011110b
               DB    11001000b
               DB    11011000b
               DB    11001000b
               DB    11011000b
               DB    01110000b

{0Fh}          DB    01111110b
               DB    10000011b
               DB    01111011b
               DB    00010011b
               DB    00011011b
               DB    00010011b
               DB    00011011b
               DB    00001110b

{10h}          DB    01111110b
               DB    01111110b
               DB    00111100b
               DB    00011000b
               DB    00011000b
               DB    00100100b
               DB    01000010b
               DB    01111110b

{11h}          DB    01111110b
               DB    01100110b
               DB    00111100b
               DB    00011000b
               DB    00011000b
               DB    00100100b
               DB    01011010b
               DB    01111110b

{12h}          DB    01111110b
               DB    01000010b
               DB    00111100b
               DB    00011000b
               DB    00011000b
               DB    00100100b
               DB    01111110b
               DB    01111110b

{13h}          DB    01111110b
               DB    01000010b
               DB    00100100b
               DB    00011000b
               DB    00011000b
               DB    00111100b
               DB    01111110b
               DB    01111110b

{14h}          DB    11100000b
               DB    10011000b
               DB    01000110b
               DB    00110001b
               DB    01101011b
               DB    01010101b
               DB    00101001b
               DB    00011110b

{15h}          DB    00000111b
               DB    00011001b
               DB    01100010b
               DB    10001100b
               DB    11010110b
               DB    10101010b
               DB    10010100b
               DB    01111000b

{16h}          DB    00011110b
               DB    00101001b
               DB    01010101b
               DB    01101011b
               DB    00110001b
               DB    01000110b
               DB    10011000b
               DB    11100000b

{17h}          DB    01111000b
               DB    10010100b
               DB    10101010b
               DB    11010110b
               DB    10001100b
               DB    01100010b
               DB    00011001b
               DB    00000111b

{18h}          DB    01100110b
               DB    10011001b
               DB    10011001b
               DB    11011101b
               DB    11011101b
               DB    10011001b
               DB    10011001b
               DB    01100110b

{19h}          DB    01100110b
               DB    11111111b
               DB    11111111b
               DB    10011001b
               DB    10011001b
               DB    10011001b
               DB    10011001b
               DB    01100110b

{1Ah}          DB    01100110b
               DB    10011001b
               DB    10011001b
               DB    10111011b
               DB    10111011b
               DB    10011001b
               DB    10011001b
               DB    01100110b

{1Bh}          DB    01100110b
               DB    10011001b
               DB    10011001b
               DB    10011001b
               DB    10011001b
               DB    11111111b
               DB    11111111b
               DB    01100110b

{1Ch}          DB    11111111b
               DB    10000010b
               DB    10000100b
               DB    10001000b
               DB    10010000b
               DB    10100000b
               DB    11000000b
               DB    10000000b

{1Dh}          DB    10000000b
               DB    11000000b
               DB    10100000b
               DB    10010000b
               DB    10001000b
               DB    10000100b
               DB    10000010b
               DB    11111111b

{1Eh}          DB    00000001b
               DB    00000011b
               DB    00000101b
               DB    00001001b
               DB    00010001b
               DB    00100001b
               DB    01000001b
               DB    11111111b

{1Fh}          DB    11111111b
               DB    01000001b
               DB    00100001b
               DB    00010001b
               DB    00001001b
               DB    00000101b
               DB    00000011b
               DB    00000001b
END;

{---[keyscan]---------------------------------------------------------------}
PROCEDURE KEYSCAN; ASSEMBLER;
ASM;
               DB    $00,$04,$0C,$22,$10,$01,$00,$00 {0: ±,3,-,g,q,esc}
               DB    $00,$03,$33,$21,$19,$2C,$00,$00 {1: ±,2,<,f,p,z}
               DB    $80,$02,$27,$12,$18,$15,$00,$00 {2: up,1,+(;),e,o,y}
               DB    $81,$0B,$0D,$20,$31,$2D,$00,$00 {3: rt,0,:(=),d,n,x}
               DB    $3A,$0E,$0A,$2E,$32,$11,$00,$00 {4: lock,del,9,c,m,w}
               DB    $29,$0F,$09,$30,$26,$2F,$00,$00 {5: ~,copy(tab),8,b,l,v}
               DB    $1B,$1C,$08,$1E,$25,$16,$00,$00 {6: ],ret,7,a,k,u}
               DB    $2B,$00,$07,$28,$24,$14,$00,$00 {7: \,±,6,@('),j,t}
               DB    $1A,$00,$06,$35,$17,$1F,$00,$00 {8: [,±,5,/,i,s}
               DB    $39,$00,$05,$34,$23,$13,$00,$00 {9: space,±,4,>,h,r}
END;

{---[altkeyscan]------------------------------------------------------------}
PROCEDURE ALTKEYSCAN; ASSEMBLER;
ASM;
               DB    $00,$04,$0C,$22,$10,$01,$00,$00 {0: ±,3,-,g,q,esc}
               DB    $00,$03,$33,$21,$19,$2C,$00,$00 {1: ±,2,<,f,p,z}
               DB    $3A,$02,$27,$12,$18,$15,$00,$00 {2: up,1,+(;),e,o,y}
               DB    $0F,$0B,$0D,$20,$31,$2D,$00,$00 {3: rt,0,:(=),d,n,x}
               DB    $4B,$0E,$0A,$2E,$32,$11,$00,$00 {4: lock,del,9,c,m,w}
               DB    $29,$4D,$09,$30,$26,$2F,$00,$00 {5: ~,copy,8,b,l,v}
               DB    $1B,$1C,$08,$1E,$25,$16,$00,$00 {6: ],ret,7,a,k,u}
               DB    $2B,$00,$07,$28,$24,$14,$00,$00 {7: \,±,6,@('),j,t}
               DB    $1A,$00,$06,$35,$17,$1F,$00,$00 {8: [,±,5,/,i,s}
               DB    $39,$00,$05,$34,$23,$13,$00,$00 {9: space,±,4,>,h,r}
END;

{---[bioscode]--------------------------------------------------------------}
PROCEDURE BIOSCODE; ASSEMBLER;
ASM;
               DW    $FFFF,$1B1B,'!1','@2','#3','$4','%5','^6'       {00}
               DW    '&7','*8','(9',')0','_-','+=',$0808,$0909       {08}
               DW    'QQ','WW','EE','RR','TT','YY','UU','II'         {10}
               DW    'OO','PP','{[','}]',$0D0D,$FFFF,'AA','SS'       {18}
               DW    'DD','FF','GG','HH','JJ','KK','LL',':;'         {20}
               DW    '"''','~`',$FFFF,'|\','ZZ','XX','CC','VV'       {28}
               DW    'BB','NN','MM','<,','>.','?/',$FFFF,'**'        {30}
               DW    $FFFF,'  ',$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF  {38}
               DW    $FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF {40}
               DW    $FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF {48}
               DW    $FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF {50}
               DW    $FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF {58}
               DW    $FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF {60}
               DW    $FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF {68}
               DW    $FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF {70}
               DW    $FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF,$FFFF {78}
END;

{---[debugtxt]--------------------------------------------------------------}
PROCEDURE DEBUGTXT; ASSEMBLER;
ASM;
               DB    00000000b,00000000b,00000000b,00000000b
               DB    01111001b,11110111b,10010001b,00111000b
               DB    01000101b,00000100b,01010001b,01000100b
               DB    01000101b,00000100b,01010001b,01000000b
               DB    01000101b,11100111b,10010001b,01011100b
               DB    01000101b,00000100b,01010001b,01000100b
               DB    01000101b,00000100b,01010001b,01000100b
               DB    01111001b,11110111b,10001111b,00111000b
               DB    00000000b,00000000b,00000000b,00000000b
               DB    00001000b,10011100b,11110011b,11100000b
               DB    00001101b,10100010b,10001010b,00000000b
               DB    00001010b,10100010b,10001010b,00000000b
               DB    00001010b,10100010b,10001011b,11000000b
               DB    00001000b,10100010b,10001010b,00000000b
               DB    00001000b,10100010b,10001010b,00000000b
               DB    00001000b,10011100b,11110011b,11100000b
               DB    00000000b,00000000b,00000000b,00000000b
END;

{---[emulcolors]------------------------------------------------------------}
PROCEDURE EMULCOLORS; ASSEMBLER;
ASM;
               DB    $00,$00,$00 {00h: backgr}
               DB    $00,$2A,$00 {01h: foregr}
               DB    $00,$15,$00 {02h: greysb}
               DB    $00,$2A,$00 {03h: color0}
               DB    $3F,$3F,$2A {04h: color1}
               DB    $00,$00,$00 {05h: color2}
               DB    $0A,$0A,$0A {06h: color3}
               DB    $00,$00,$00 {07h: randkleur}
               DB    $00,$00,$2A {08h: blauw}
               DB    $34,$00,$00 {09h: rood}
               DB    $20,$10,$00 {0Ah: bruin}
               DB    $20,$20,$20 {0Bh: grijs}
               DB    $15,$3F,$15 {0Ch: licht groen}
               DB    $00,$00,$00 {0Dh: zwart}
               DB    $3F,$3F,$15 {0Eh: geel}
               DB    $3F,$3F,$3F {0Fh: wit}
END;

{---[intensmono]------------------------------------------------------------}
PROCEDURE INTENSMONO; ASSEMBLER;
ASM;
               DB    $00,$3F,$00
END;

{---[intenscolor]-----------------------------------------------------------}
PROCEDURE INTENSCOLOR; ASSEMBLER;
ASM;
               DB    $00,$1C,$00
END;

{---[pcwaittable (filled depending on CPU speed)]---------------------------}
PROCEDURE PCWAITTABLE; ASSEMBLER;
ASM;
               DW    0
               DW    0
               DW    0
               DW    0
               DW    0
               DW    0
               DW    0
               DW    0
               DW    0
END;

{---[wachtconst (if specified in .INI file)]--------------------------------}
PROCEDURE WACHTCONST; ASSEMBLER;
ASM;
               DW    $0000
END;

{---[cursorx]---------------------------------------------------------------}
PROCEDURE CURSORX; ASSEMBLER;
ASM;
END;

{---[cursory]---------------------------------------------------------------}
PROCEDURE CURSORY; ASSEMBLER;
ASM;
END;

{---[dataseg (word)]--------------------------------------------------------}
PROCEDURE DATASEG; ASSEMBLER;
ASM;
               DB    $00
END;

{---[sortdir]---------------------------------------------------------------}
PROCEDURE SORTDIR (VAR A:FILELISTTYPE; LO,HI:INTEGER);
VAR X,Y:STR8;

  PROCEDURE SORTEER (L,R:INTEGER);
  VAR I,J:INTEGER;
  BEGIN
    I := L;
    J := R;
    X := A[(L+R) DIV 2];
    REPEAT
      WHILE A[I] < X DO INC (I);
      WHILE X < A[J] DO DEC (J);
      IF I <= J THEN
      BEGIN
        Y := A[I];
        A[I] := A[J];
        A[J] := Y;
        INC (I);
        DEC (J);
      END;
    UNTIL I > J;
    IF L < J THEN SORTEER (L,J);
    IF I < R THEN SORTEER (I,R);
  END;

BEGIN
  SORTEER (LO,HI);
END;

{---[readdirectory]---------------------------------------------------------}
PROCEDURE READDIRECTORY;
VAR D:SEARCHREC;
    I:WORD;
BEGIN
  AANTALATOMFILES := 0;
  AANTALTAPEIMAGES := 0;
  FINDFIRST ('*.TAP',ANYFILE,D);
  WHILE (DOSERROR = 0) AND (AANTALTAPEIMAGES < MAXAANTFILES) DO
  BEGIN
    IF D.ATTR AND $18 = $00 THEN
    BEGIN
      D.NAME := COPY(D.NAME,1,LENGTH(D.NAME)-4);
      TAPEIMAGES[AANTALTAPEIMAGES] := D.NAME;
      INC (AANTALTAPEIMAGES);
    END;
    FINDNEXT (D);
  END;
  IF AANTALTAPEIMAGES > 0 THEN SORTDIR (TAPEIMAGES,0,PRED(AANTALTAPEIMAGES));
  AANTALDISKIMAGES := 0;
  FINDFIRST ('*.DSK',ANYFILE,D);
  WHILE (DOSERROR = 0) AND (AANTALDISKIMAGES < MAXAANTFILES) DO
  BEGIN
    IF (D.ATTR AND (VOLUMEID OR DIRECTORY) = $00) AND (D.SIZE=40*10*256) THEN
    BEGIN
      D.NAME := COPY(D.NAME,1,LENGTH(D.NAME)-4);
      DISKIMAGES[AANTALDISKIMAGES] := D.NAME;
      INC (AANTALDISKIMAGES);
    END;
    FINDNEXT (D);
  END;
  IF AANTALDISKIMAGES > 0 THEN SORTDIR (DISKIMAGES,0,PRED(AANTALDISKIMAGES));
END;

{---[copywriteprot]---------------------------------------------------------}
PROCEDURE COPYWRITEPROT;
CONST WP:ARRAY[0..1] OF BYTE = ($0F,$F0);
VAR I,J:BYTE;
    D:SEARCHREC;
BEGIN
  WRITEPROTECT[$00] := $00;
  WRITEPROTECT[$01] := $00;
  FOR I := 0 TO 3 DO
  BEGIN
    IF DISKETTENAMES[I] <> '' THEN
    BEGIN
      FINDFIRST (DISKETTENAMES[I]+'.DSK',ANYFILE,D);
      IF DOSERROR=0 THEN
      BEGIN
        J := D.ATTR AND READONLY;
        IF J <> 0 THEN
          WRITEPROTECT[I AND 1] := WRITEPROTECT[I AND 1] OR WP[I SHR 1]
      END ELSE
      BEGIN
        DISKETTENAMES[I] := '';
      END;
    END;
  END;
END;

{---[readfilesintapeimage]--------------------------------------------------}
PROCEDURE READFILESINTAPEIMAGE;
VAR FROMF    : FILE;
    TAPESIZE : LONGINT;
    FPOS     : LONGINT;
    NR       : WORD;
    DUMMY    : INTEGER;
BEGIN
  DUMMY := IORESULT;
  AANTALATOMFILES := 0;
  IF LENGTH(TAPEIMAGENAME) = 0 THEN EXIT;
  ASSIGN (FROMF,TAPEIMAGENAME+'.TAP');
  RESET (FROMF,1);
  IF IORESULT <> 0 THEN EXIT;
  TAPESIZE := FILESIZE (FROMF);
  FPOS := 0;
  WHILE FPOS < TAPESIZE DO
  BEGIN
    SEEK (FROMF,FPOS);
    BLOCKREAD (FROMF,ATOMFILES[AANTALATOMFILES],SIZEOF(ATMFILEREC),NR);
    IF NR <> SIZEOF(ATMFILEREC) THEN
    BEGIN
      CLOSE (FROMF);
      EXIT;
    END;
    INC (FPOS,SIZEOF(ATMFILEREC)+LONGINT(ATOMFILES[AANTALATOMFILES].DATASIZE));
    INC (AANTALATOMFILES);
  END;
  CLOSE (FROMF);
END;

{---[tempdosprompt]---------------------------------------------------------}
PROCEDURE TEMPDOSPROMPT;
VAR CURDIR:STRING;
    I:BYTE;
    J:WORD;
BEGIN
  GETDIR (0,CURDIR);
  ASM;
               MOV   AX,$0003
               INT   $10
  END;
  WRITELN;
  WRITELN ('               Type EXIT to return to the Acorn Atom Emulator...');
  ASM;
                MOV   AX,$B800
                MOV   ES,AX
                MOV   BX,$0001
  @TDP1:        MOV   BYTE PTR [ES:BX],$1E
                ADD   BX,+$02
                CMP   BX,+481
                JB    @TDP1
  END;
  EXEC (GETENV('COMSPEC'),'');
  CHDIR (CURDIR);
  READDIRECTORY;
  COPYWRITEPROT;
  READFILESINTAPEIMAGE;
END;

{---[nextline]--------------------------------------------------------------}
PROCEDURE NEXTLINE; ASSEMBLER;
ASM;
               MOV   BYTE PTR [CS:CURSORX],$00
               INC   BYTE PTR [CS:CURSORY]
               CMP   BYTE PTR [CS:CURSORY],+19
               JB    @NEXTLINE1
               PUSHA
               DEC   BYTE PTR [CS:CURSORY]
               CLI
               MOV   DI,+20*$0120
               MOV   SI,+30*$0120
               MOV   CX,(200-30)*$0120/2
               REPZ
               MOVSW
               MOV   CX,+10*$0120/2
               SUB   AX,AX
               REPZ
               STOSW
               STI
               POPA
@NEXTLINE1:
END;

{---[printchar; AL=char; BL=color (used by desktop)]------------------------}
PROCEDURE PRINTCHAR; ASSEMBLER;
ASM;
               PUSH  DS
               PUSHA
               MOV   DI,SEG CHARDATA
               MOV   DS,DI
               MOV   AH,$00
               SHL   AX,4
               ADD   AX,OFFSET CHARDATA
               ADD   AX,+2
               MOV   SI,AX
               MOV   AL,BYTE PTR [CS:CURSORY]
               MOV   AH,$00
               MOV   CX,10*$0120
               MUL   CX
               ADD   AX,$0140
               MOV   DI,AX
               MOV   AL,BYTE PTR [CS:CURSORX]
               ADD   AL,+12
               MOV   AH,$00
               SHL   AX,2
               ADD   DI,AX
               MOV   CH,+10
@PRINTCH4:     LODSB
               MOV   AH,$01
@PRINTCH5:     TEST  BL,AH
               JZ    @PRINTCH1
               CMP   AH,$02
               JNZ   @PRINTCH6
               STOSB
               JMP   @PRINTCH2
@PRINTCH6:     MOV   BYTE PTR [ES:DI],$FF
               INC   DI
               JMP   @PRINTCH2
@PRINTCH1:     CMP   AH,$02
               JNZ   @PRINTCH7
               MOV   BYTE PTR [ES:DI],$00
               INC   DI
               JMP   @PRINTCH2
@PRINTCH7:     NOT   AL
               STOSB
               NOT   AL
@PRINTCH2:     SHL   AH,1
               CMP   AH,$10
               JB    @PRINTCH5
               ADD   DI,$011C
               DEC   CH
               JNZ   @PRINTCH4
               INC   BYTE PTR [CS:CURSORX]
               CMP   BYTE PTR [CS:CURSORX],+40
               JB    @PRINTCH3
               CALL  NEXTLINE
@PRINTCH3:     POPA
               POP   DS
END;

{---[xorput; DI=screenpos; AL=color (00h-0Fh); CX=length]-------------------}
PROCEDURE XORPUT; ASSEMBLER;
ASM;
               PUSH  AX
               PUSH  BX
               PUSH  CX
               PUSH  DX
               MOV   BYTE PTR @XORPKLR,AL
               MOV   DL,+9
@XORP6:        PUSH  DX
               PUSH  DI
               PUSH  CX
@XORP5:        PUSH  CX
               MOV   DL,BYTE PTR @XORPKLR
               MOV   CL,$0D
               MOV   AX,$FFFF
               SUB   BX,BX
@XORP2:        MOV   DH,BYTE PTR [ES:DI+BX]
               SHR   DL,1
               JC    @XORP1
               NOT   DH
@XORP1:        AND   AL,DH
               MOV   DH,BYTE PTR [ES:DI+BX]
               SHR   CL,1
               JC    @XORP7
               NOT   DH
@XORP7:        AND   AH,DH
               INC   BL
               CMP   BL,$04
               JNZ   @XORP2
               POP   CX
               {AL geeft posities van kleur aan; AH van zwart (0Dh)}
               OR    BYTE PTR [ES:DI],AL
               NOT   AL
               AND   BYTE PTR [ES:DI+$01],AL
               NOT   AL
               OR    BYTE PTR [ES:DI+$02],AL
               OR    BYTE PTR [ES:DI+$03],AL
               MOV   AL,AH
               NOT   AL
               MOV   DL,BYTE PTR @XORPKLR
               SUB   BX,BX
@XORP4:        AND   BYTE PTR [ES:DI+BX],AL
               SHR   DL,1
               JNC   @XORP3
               OR    BYTE PTR [ES:DI+BX],AH
@XORP3:        INC   BL
               CMP   BL,$04
               JNZ   @XORP4
               ADD   DI,+$04
               LOOP  @XORP5
               POP   CX
               POP   DI
               POP   DX
               ADD   DI,$0120
               DEC   DL
               JNZ   @XORP6
               POP   DX
               POP   CX
               POP   BX
               POP   AX
               RETN
@XORPKLR:
END;

{---[altkeyb (one byte)]----------------------------------------------------}
PROCEDURE ALTKEYB; ASSEMBLER;
ASM;
END;

{---[swapkeyboard]----------------------------------------------------------}
PROCEDURE SWAPKEYBOARD; ASSEMBLER;
ASM;
               PUSHA
               MOV   BYTE PTR [CS:CURSORX],+9
               MOV   BYTE PTR [CS:CURSORY],+8
               MOV   BL,$09
               MOV   AL,01000101b
               CALL  PRINTCHAR
               MOV   CX,+20
               MOV   AL,01001100b
@SWAP1:        CALL  PRINTCHAR
               LOOP  @SWAP1
               MOV   AL,01001010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+9
               MOV   BYTE PTR [CS:CURSORY],+9
               MOV   AL,01010101b
               CALL  PRINTCHAR
               MOV   SI,OFFSET @STANDARDTXT
               XOR   BYTE PTR [CS:ALTKEYB],$01
               JZ    @SWAP3
               MOV   SI,OFFSET @ALTERNATETXT
@SWAP3:        MOV   BL,$0C
@SWAP5:        MOV   AL,BYTE PTR [CS:SI]
               INC   SI
               AND   AL,$3F
               JZ    @SWAP4
               CALL  PRINTCHAR
               JMP   @SWAP5
@SWAP4:        MOV   BL,$09
               MOV   AL,01101010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+9
               MOV   BYTE PTR [CS:CURSORY],+10
               MOV   AL,01010100b
               CALL  PRINTCHAR
               MOV   CX,+20
               MOV   AL,01001100b
@SWAP2:        CALL  PRINTCHAR
               LOOP  @SWAP2
               MOV   AL,01101000b
               CALL  PRINTCHAR
               POPA
               RETN
@ALTERNATETXT: DB    ' ALTERNATE KEYBOARD ',$00
@STANDARDTXT:  DB    ' STANDARD KEYBOARD  ',$00
END;

{---[cpuspeedmode]----------------------------------------------------------}
PROCEDURE CPUSPEEDMODE; ASSEMBLER;
ASM;
END;

{---[asmlayout]-------------------------------------------------------------}
PROCEDURE ASMLAYOUT; ASSEMBLER;
ASM;
END;

{---[soundoutput]-----------------------------------------------------------}
PROCEDURE SOUNDOUTPUT; ASSEMBLER;
ASM;
END;

{---[boxswitch (byte)]------------------------------------------------------}
PROCEDURE BOXSWITCH; ASSEMBLER; {use boxswitching; 00h=no; 01h=yes}
ASM;
END;

{---[box0onbreak (byte)]----------------------------------------------------}
PROCEDURE BOX0ONBREAK; ASSEMBLER; {restore box 0 on break; 00h=no; 01h=yes}
ASM;
END;

{---[ignorezpFEh (byte)]----------------------------------------------------}
PROCEDURE IGNOREzpFEh; ASSEMBLER; {ignore check char not sent to printer}
ASM;
END;

{---[nmiresponse (byte)]----------------------------------------------------}
PROCEDURE NMIRESPONSE; ASSEMBLER;
ASM;
END;

{---[leendertsrom (byte): use 80x87 or not]---------------------------------}
PROCEDURE LEENDERTSROM; ASSEMBLER;
ASM;
END;

{---[abloksprong (word): offset for JMP A002h in D-block]-------------------}
PROCEDURE ABLOKSPRONG; ASSEMBLER;
ASM;
               DB    $00
END;

{---[fppc_addr (dword)]-----------------------------------------------------}
PROCEDURE FPPC_ADDR; ASSEMBLER;
ASM;
               DB    0,0,0
END;

{---[swapcpuspeed]----------------------------------------------------------}
PROCEDURE SWAPCPUSPEED; ASSEMBLER;
ASM;
               PUSHA
               MOV   BYTE PTR [CS:CURSORX],+9
               MOV   BYTE PTR [CS:CURSORY],+8
               MOV   BL,$09
               MOV   AL,01000101b
               CALL  PRINTCHAR
               MOV   CX,+20
               MOV   AL,01001100b
@SWAP1:        CALL  PRINTCHAR
               LOOP  @SWAP1
               MOV   AL,01001010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+9
               MOV   BYTE PTR [CS:CURSORY],+9
               MOV   AL,01010101b
               CALL  PRINTCHAR
               MOV   SI,OFFSET @ORIGINALTXT
               XOR   BYTE PTR [CS:CPUSPEEDMODE],$01
               JZ    @SWAP3
               MOV   SI,OFFSET @MAXIMUMTXT
@SWAP3:        MOV   BL,$0C
@SWAP5:        MOV   AL,BYTE PTR [CS:SI]
               INC   SI
               AND   AL,$3F
               JZ    @SWAP4
               CALL  PRINTCHAR
               JMP   @SWAP5
@SWAP4:        MOV   BL,$09
               MOV   AL,01101010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+9
               MOV   BYTE PTR [CS:CURSORY],+10
               MOV   AL,01010100b
               CALL  PRINTCHAR
               MOV   CX,+20
               MOV   AL,01001100b
@SWAP2:        CALL  PRINTCHAR
               LOOP  @SWAP2
               MOV   AL,01101000b
               CALL  PRINTCHAR
               POPA
               RETN
@MAXIMUMTXT:   DB    ' MAXIMUM CPU SPEED  ',$00
@ORIGINALTXT:  DB    ' ORIGINAL CPU SPEED ',$00
END;

{---[hex (byte)]------------------------------------------------------------}
FUNCTION HEX (B:BYTE):STR2;
BEGIN
  HEX := HEXSTR[B SHR 4] + HEXSTR[B AND $0F];
END;

{---[hexw (word)]-----------------------------------------------------------}
FUNCTION HEXW (W:WORD):STR4;
BEGIN
  HEXW := HEXSTR[HI(W) SHR 4] + HEXSTR[HI(W) AND $0F] +
          HEXSTR[LO(W) SHR 4] + HEXSTR[LO(W) AND $0F];
END;

{---[readinifile]-----------------------------------------------------------}
PROCEDURE READINIFILE;
LABEL 1;
CONST INI_BYTE : ARRAY[1..8] OF STRING[11] =
               ('ASMLAYOUT','SOUND','SPEEDINDEX','BOXSWITCH',
                'BOX0ONBREAK','IGNOREZPFEH','NMIRESPONSE','USE80X87');
      INI_STR  : ARRAY[1..9] OF STRING[10] =
                ('EXTROMFILE','BACKGR','FOREGR','GREYSB',
                 'COLOR0','COLOR1','COLOR2','COLOR3','DRIVE');
      PCHARMESTR = 'P-CHARME'+#0+#0+#0+#0+#0+#0+#0+#0;
VAR F:TEXT;
    S:STRING;
    R,G,I:BYTE;
    B:WORD;
    CODE:INTEGER;
    FROMF:FILE;
    NR:WORD;
    DUMMY:INTEGER;
    P,Q:POINTER;
    ATMHEADER:ATMFILEREC;
BEGIN
  WRITE ('Seaching for INI-file.');
  ASM;
               MOV   BYTE PTR [CS:ASMLAYOUT],$00
               MOV   BYTE PTR [CS:SOUNDOUTPUT],$01
               MOV   WORD PTR [CS:WACHTCONST],$0000
               MOV   BYTE PTR [CS:BOXSWITCH],$01
               MOV   BYTE PTR [CS:BOX0ONBREAK],$01
               MOV   BYTE PTR [CS:IGNOREzpFEh],$01
               MOV   BYTE PTR [CS:NMIRESPONSE],+15
               MOV   BYTE PTR [CS:LEENDERTSROM],$00
               MOV   WORD PTR [CS:ABLOKSPRONG],$D4BE
  END;
  EXTROMFILE := 'EXTROM.TAP';
  DUMMY := IORESULT;
  ASSIGN (F,'ATOM.INI');
  RESET (F);
  IF IORESULT <> 0 THEN
  BEGIN
    WRITELN (' Not found.');
    GOTO 1;
  END ELSE
  BEGIN
    WRITELN (' Reading.');
  END;
  WHILE NOT EOF(F) DO
  BEGIN
    READLN (F,S);
    FOR I := 1 TO LENGTH(S) DO S[I] := UPCASE(S[I]);
    FOR I := 1 TO 8 DO
    BEGIN
      IF COPY(S,1,LENGTH(INI_BYTE[I]))=INI_BYTE[I] THEN
      BEGIN
        DELETE (S,1,SUCC(LENGTH(INI_BYTE[I])));
        VAL (S,B,CODE);
        IF CODE = 0 THEN
        BEGIN
          CASE I OF 1: ASM;
                            MOV   AX,WORD PTR B
                            OR    AX,AX
                            JZ    @R1
                            MOV   AL,$01
                       @R1: MOV   BYTE PTR [CS:ASMLAYOUT],AL
                       END;
                    2: ASM;
                            MOV   AX,WORD PTR B
                            OR    AX,AX
                            JZ    @R2
                            MOV   AL,$01
                       @R2: MOV   BYTE PTR [CS:SOUNDOUTPUT],AL
                       END;
                    3: ASM;
                            MOV   AX,WORD PTR B
                            MOV   WORD PTR [CS:WACHTCONST],AX
                       END;
                    4: ASM;
                            MOV   AX,WORD PTR B
                            OR    AX,AX
                            JZ    @R4
                            MOV   AL,$01
                       @R4: MOV   BYTE PTR [CS:BOXSWITCH],AL
                       END;
                    5: ASM;
                            MOV   AX,WORD PTR B
                            OR    AX,AX
                            JZ    @R5
                            MOV   AL,$01
                       @R5: MOV   BYTE PTR [CS:BOX0ONBREAK],AL
                       END;
                    6: ASM;
                            MOV   AX,WORD PTR B
                            OR    AX,AX
                            JZ    @R6
                            MOV   AL,$01
                            MOV   ES,WORD PTR ATOMMEMSEG
                            MOV   BYTE PTR [ES:$FF07],$00
                       @R6: MOV   BYTE PTR [CS:IGNOREzpFEh],AL
                       END;
                    7: ASM;
                            MOV   AX,WORD PTR B
                            CMP   AL,+15
                            JAE   @R7
                            MOV   AL,+15
                       @R7: MOV   BYTE PTR [CS:NMIRESPONSE],AL
                       END;
                    8: ASM;
                            MOV   AX,WORD PTR B
                            OR    AX,AX
                            JZ    @R8
                            MOV   AL,$01
                       @R8: MOV   BYTE PTR [CS:LEENDERTSROM],AL
                       END;
          END;
        END;
      END;
    END;
    FOR I := 1 TO 9 DO
    BEGIN
      IF COPY(S,1,LENGTH(INI_STR[I]))=INI_STR[I] THEN
      BEGIN
        DELETE (S,1,LENGTH(INI_STR[I]));
        IF I=1 THEN
        BEGIN
          DELETE (S,1,1);
          IF LENGTH(S) > 0 THEN EXTROMFILE := S;
        END ELSE
        IF I=9 THEN
        BEGIN
          G := ORD(S[1]);
          DEC (G,48);
          IF G <= 3 THEN
          BEGIN
            DELETE (S,1,2);
            IF COPY (S,LENGTH(S)-3,4)='.DSK' THEN DEC (S[0],4);
            IF (S <> '') AND (AANTALDISKIMAGES > 0) THEN
            BEGIN
              B := 0;
              WHILE (DISKETTENAMES[G] = '') AND (B < AANTALDISKIMAGES) DO
              BEGIN
                IF S=DISKIMAGES[B] THEN DISKETTENAMES[G] := S;
                INC (B);
              END;
            END;
          END;
        END ELSE
        BEGIN
          DELETE (S,1,1);
          IF LENGTH(S)=6 THEN
          BEGIN
            FOR B := 1 TO LENGTH(S) DO
            BEGIN
              S[B] := CHR(ORD(S[B])-48);
              IF ORD(S[B]) > 9 THEN S[B] := CHR(ORD(S[B])-7);
            END;
            R := (ORD(S[1]) SHL 4) + ORD(S[2]);
            G := (ORD(S[3]) SHL 4) + ORD(S[4]);
            B := (ORD(S[5]) SHL 4) + ORD(S[6]);
            ASM;
               MOV   AL,BYTE PTR I
               SUB   AL,$02
               MOV   AH,$00
               MOV   BX,AX
               SHL   AX,1
               ADD   BX,AX
               MOV   AL,BYTE PTR R
               AND   AL,$3F
               MOV   BYTE PTR EMULCOLORS[CS:BX],AL
               MOV   AL,BYTE PTR G
               AND   AL,$3F
               MOV   BYTE PTR EMULCOLORS[CS:BX+$01],AL
               MOV   AL,BYTE PTR B
               AND   AL,$3F
               MOV   BYTE PTR EMULCOLORS[CS:BX+$02],AL
            END;
          END;
        END;
      END;
    END;
  END;
  CLOSE (F);
  FOR I := 3 DOWNTO 1 DO
    FOR G := I-1 DOWNTO 0 DO
      IF DISKETTENAMES[I] = DISKETTENAMES[G] THEN DISKETTENAMES[I] := '';
1:ASM;
               PUSH  DS
               POP   ES
               MOV   DI,OFFSET BOXNAMES
               MOV   AL,$00
               MOV   CX,+16*16
               CLD
               REPZ
               STOSB
  END;
  IF MEM[CSEG:OFS(LEENDERTSROM)] <> $00 THEN
  BEGIN
    ASM;
               CLD
               MOV   ES,WORD PTR ATOMMEMSEG
               MOV   SI,OFFSET LEENDERTS_FPROM_DAT
               MOV   DI,$D000
               MOV   CX,LEENDERTS_FPROM_SIZE
               REPZ
               MOVSB
    END;
    GETMEM (P,SIZEOF(FPPC_DAT)+$0010);
    B := SEG(P^);
    IF OFS(P^) <> $0000 THEN INC (B);
    MOVE (FPPC_DAT,MEM[B:$0000],SIZEOF(FPPC_DAT));
    ASM;
               MOV   WORD PTR FPPC_ADDR[CS:$00],$0000
               MOV   AX,WORD PTR B
               MOV   WORD PTR FPPC_ADDR[CS:$02],AX
    END;
  END;
  DUMMY := IORESULT;
  ASSIGN (FROMF,EXTROMFILE);
  RESET (FROMF,1);
  IF IORESULT = 0 THEN
  BEGIN
    B := 0;
    WHILE (B < 16) AND (NOT EOF(FROMF)) DO
    BEGIN
      BLOCKREAD (FROMF,ATMHEADER,SIZEOF(ATMHEADER),NR);
      IF (IORESULT = 0) AND (NR=$16) THEN
      BEGIN
        IF (ATMHEADER.STARTADRS = $A000) AND (ATMHEADER.DATASIZE = $1000) THEN
        BEGIN
          MOVE (ATMHEADER.ATMNAME,BOXNAMES[B],$10);
          P := PTR (ATOMMEMSEG+$1000,B*$1000);
          BLOCKREAD (FROMF,P^,$1000,NR);
          IF (MEM[CSEG:OFS(LEENDERTSROM)] <> 0) AND (BOXNAMES[B] = PCHARMESTR) THEN
          BEGIN
            ASM;
               {---initialize the P-Charme for Leendert's FP-ROM---}
               PUSH  DS
               MOV   AX,WORD PTR ATOMMEMSEG
               MOV   DS,AX
               MOV   BH,BYTE PTR B
               MOV   BL,$00
               ADD   AX,BX
               ADD   AX,$1000-$0A00
               MOV   ES,AX {segment of p-charme, when offset = A000h}
               MOV   SI,$DEF0
               MOV   AX,WORD PTR [SI]
               MOV   WORD PTR [CS:ABLOKSPRONG],AX
               MOV   AX,WORD PTR [SI+$02]
               MOV   WORD PTR [ES:$A591+1],AX
               MOV   WORD PTR [ES:$A66E+1],AX
               SUB   AX,$000A
               MOV   WORD PTR [ES:$A79A+1],AX
               SUB   AX,$003C-$000A
               MOV   WORD PTR [ES:$A9D4+1],AX
               SUB   AX,$0015-$003C
               MOV   WORD PTR [ES:$AB07+1],AX
               MOV   WORD PTR [ES:$AB25+1],AX
               MOV   AX,WORD PTR [SI+$04]
               MOV   WORD PTR [ES:$A598+1],AX
               MOV   WORD PTR [ES:$AB1F+1],AX
               SUB   AX,$0007
               MOV   WORD PTR [ES:$A9C8+1],AX
               MOV   AX,WORD PTR [SI+$06]
               MOV   WORD PTR [ES:$A952+1],AX
               MOV   AX,WORD PTR [SI+$08]
               MOV   WORD PTR [ES:$AB04+1],AX
               ADD   AX,$0061
               MOV   WORD PTR [ES:$AB19+1],AX
               MOV   AX,WORD PTR [SI+$0A]
               MOV   WORD PTR [ES:$AB22+1],AX
               MOV   AX,WORD PTR [SI+$0C]
               MOV   WORD PTR [ES:$AD86+1],AX
               MOV   AX,WORD PTR [SI+$0E]
               MOV   WORD PTR [ES:$AF09+1],AX
               MOV   AX,WORD PTR [SI+$10]
               MOV   WORD PTR [ES:$AF10+1],AX
               POP   DS
            END;
          END;
          INC (B);
        END ELSE
        BEGIN
          SEEK (FROMF,FILEPOS(FROMF)+LONGINT(ATMHEADER.DATASIZE));
          NR := $1000;
        END;
      END ELSE
      BEGIN
        NR := 0;
      END;
      IF NR <> $1000 THEN
      BEGIN
        WRITELN ('Error while loading extension ROMs.');
        CLOSE (FROMF);
        HALT (1);
      END;
    END;
    CLOSE (FROMF);
    {---load EPROM box 0 into Atom memory---}
    P := PTR (ATOMMEMSEG+$1000,$0000);
    Q := PTR (ATOMMEMSEG,$A000);
    MOVE (P^,Q^,$1000);
  END ELSE
  BEGIN
    WRITELN ('No extension ROMs loaded.');
    {---only AXR1 available---}
    P := PTR (ATOMMEMSEG,$A000);
    Q := PTR (ATOMMEMSEG+$1000,$0000);
    MOVE (P^,Q^,$1000);
    BOXNAMES[0,0] := 'A';
    BOXNAMES[0,1] := 'X';
    BOXNAMES[0,2] := 'R';
    BOXNAMES[0,3] := '1';
  END;
END;

{---[writeinifile]----------------------------------------------------------}
PROCEDURE WRITEINIFILE;
VAR F:TEXT;
    B:BYTE;
    W:WORD;
    S:STRING[6];
    DUMMY:INTEGER;
BEGIN
  DUMMY := IORESULT;
  ASSIGN (F,'ATOM.INI');
  REWRITE (F);
  IF IORESULT <> 0 THEN EXIT;
  WRITELN (F,'[Config]');
  B := MEM[CSEG:OFS(ASMLAYOUT)];
  IF B > 0 THEN B := 1;
  WRITELN (F,'ASMLayout=',B);
  B := MEM[CSEG:OFS(SOUNDOUTPUT)];
  IF B > 0 THEN B := 1;
  WRITELN (F,'Sound=',B);
  W := MEMW[CSEG:OFS(WACHTCONST)];
  WRITE (F,'SpeedIndex=');
  IF W > 0 THEN WRITELN (F,W)
           ELSE WRITELN (F);
  WRITELN (F,'ExtROMFile=',EXTROMFILE);
  B := MEM[CSEG:OFS(LEENDERTSROM)];
  IF B > 0 THEN B := 1;
  WRITELN (F,'Use80x87=',B);
  WRITELN (F);
  WRITELN (F,'[Emulation]');
  B := MEM[CSEG:OFS(IGNOREzpFEh)];
  IF B > 0 THEN B := 1;
  WRITELN (F,'IgnoreZpFEh=',B);
  B := MEM[CSEG:OFS(BOXSWITCH)];
  IF B > 0 THEN B := 1;
  WRITELN (F,'BoxSwitch=',B);
  B := MEM[CSEG:OFS(BOX0ONBREAK)];
  IF B > 0 THEN B := 1;
  WRITELN (F,'Box0onBreak=',B);
  B := MEM[CSEG:OFS(NMIRESPONSE)];
  IF B < 15 THEN B := 15;
  WRITELN (F,'NMIResponse=',B);
  WRITELN (F);
  WRITELN (F,'[Colors]');
  S := '';
  FOR B := 0 TO 2 DO
    S := S + HEX(MEM[CSEG:OFS(EMULCOLORS)+0*3+B]);
  WRITELN (F,'BackGr=',S);
  S := '';
  FOR B := 0 TO 2 DO
    S := S + HEX(MEM[CSEG:OFS(EMULCOLORS)+1*3+B]);
  WRITELN (F,'ForeGr=',S);
  S := '';
  FOR B := 0 TO 2 DO
    S := S + HEX(MEM[CSEG:OFS(EMULCOLORS)+2*3+B]);
  WRITELN (F,'GreySb=',S);
  S := '';
  FOR B := 0 TO 2 DO
    S := S + HEX(MEM[CSEG:OFS(EMULCOLORS)+3*3+B]);
  WRITELN (F,'Color0=',S);
  S := '';
  FOR B := 0 TO 2 DO
    S := S + HEX(MEM[CSEG:OFS(EMULCOLORS)+4*3+B]);
  WRITELN (F,'Color1=',S);
  S := '';
  FOR B := 0 TO 2 DO
    S := S + HEX(MEM[CSEG:OFS(EMULCOLORS)+5*3+B]);
  WRITELN (F,'Color2=',S);
  S := '';
  FOR B := 0 TO 2 DO
    S := S + HEX(MEM[CSEG:OFS(EMULCOLORS)+6*3+B]);
  WRITELN (F,'Color3=',S);
  WRITELN (F);
  WRITELN (F,'[Disk]');
  FOR B := 0 TO 3 DO
  BEGIN
    WRITE (F,'Drive',B,'=');
    IF DISKETTENAMES[B] <> '' THEN WRITE (F,DISKETTENAMES[B],'.DSK');
    WRITELN (F);
  END;
  CLOSE (F);
END;

{---[outbyte (output byte to dsp)]------------------------------------------}
PROCEDURE OUTBYTE; ASSEMBLER;
ASM;
               MOV   AH,AL
@OUTB1:        IN    AL,DX
               OR    AL,AL
               JS    @OUTB1
               MOV   AL,AH
               OUT   DX,AL
END;

{---[sbsound]---------------------------------------------------------------}
PROCEDURE SBSOUND; ASSEMBLER;
ASM;
               PUSH  DS
               PUSH  DX
               MOV   AX,SEG IOPORT
               MOV   DS,AX
               MOV   DX,WORD PTR IOPORT
               ADD   DL,$0C
               MOV   AL,$10
               CALL  OUTBYTE
               MOV   AL,BYTE PTR @SOUNDBYTE
               CALL  OUTBYTE
               XOR   BYTE PTR @SOUNDBYTE,11000000b
               POP   DX
               POP   DS
               RETN
@SOUNDBYTE:    DB    01100000b
END;

{---[errorsnd]--------------------------------------------------------------}
PROCEDURE ERRORSND; ASSEMBLER;
ASM;
               PUSH  DS
               PUSH  DX
               MOV   DX,WORD PTR IOPORT
               ADD   DL,$0C
               MOV   DS,WORD PTR ATOMMEMSEG
               MOV   CX,$0800
@ERRORSND3:    PUSH  CX
@ERRORSND2:    MOV   AX,WORD PTR PCWAITTABLE[CS:$0002]
@ERRORSND1:    DEC   AX
               JNZ   @ERRORSND1
               LOOP  @ERRORSND2
               CMP   DX,+$0C
               JNZ   @ERRORSND4
               IN    AL,$61
               XOR   AL,$02
               OUT   $61,AL
               JMP   @ERRORSND5
@ERRORSND4:    CALL  SBSOUND
@ERRORSND5:    POP   CX
               SUB   CX,+$10
               CMP   CX,$0020
               JAE   @ERRORSND3
               POP   DX
               POP   DS
END;

{---[fouterrorsnd]----------------------------------------------------------}
PROCEDURE FOUTERRORSND; ASSEMBLER;
ASM;
               PUSH  DS
               PUSH  BX
               PUSH  DX
               MOV   BL,$03
@ERRORSND6:    MOV   DX,WORD PTR IOPORT
               ADD   DL,$0C
               MOV   DS,WORD PTR ATOMMEMSEG
               MOV   CX,$0040
@ERRORSND3:    PUSH  CX
@ERRORSND2:    MOV   AX,WORD PTR PCWAITTABLE[CS:$0002]
@ERRORSND1:    DEC   AX
               JNZ   @ERRORSND1
               LOOP  @ERRORSND2
               CMP   DX,+$0C
               JNZ   @ERRORSND4
               IN    AL,$61
               XOR   AL,$02
               OUT   $61,AL
               JMP   @ERRORSND5
@ERRORSND4:    CALL  SBSOUND
@ERRORSND5:    POP   CX
               ADD   CX,+$20
               CMP   CX,$0700
               JB    @ERRORSND3
               DEC   BL
               JNZ   @ERRORSND6
               POP   DX
               POP   BX
               POP   DS
END;

{---[makewider; AL=byte; return: AX=word]-----------------------------------}
PROCEDURE MAKEWIDER; ASSEMBLER;
ASM;
               PUSH  BX
               MOV   BL,AL
               SUB   AX,AX
               MOV   BH,$08
@MAKEW1:       SHL   BL,1
               JNC   @MAKEW2
               RCL   AX,1
               STC
               RCL   AX,1
               JMP   @MAKEW3
@MAKEW2:       SHL   AX,2
@MAKEW3:       DEC   BH
               JNZ   @MAKEW1
               POP   BX
END;

{---[initialize]------------------------------------------------------------}
PROCEDURE INITIALIZE;
CONST EMUDETECT : ARRAY[0..64] OF CHAR =
        'ACORN ATOM EMULATOR V1.33 (C) BYWOUTER RAS, DELFT, OCT''97-MAY''99'+#$0D;
VAR I:WORD;
BEGIN
  {---reset dsp---}
  ASM;
               MOV   WORD PTR IOPORT,$0210
  @RESDSP7:    MOV   DX,WORD PTR IOPORT
               ADD   DL,$06
               MOV   AL,$01
               OUT   DX,AL
               MOV   CX,$0400
  @RESDSP1:    LOOP  @RESDSP1
               MOV   AL,$00
               OUT   DX,AL
               MOV   BL,$10
  @RESDSP3:    MOV   DX,WORD PTR IOPORT
               ADD   DL,$0E
               MOV   CX,$0100
  @RESDSP2:    IN    AL,DX
               TEST  AL,$80
               JNZ   @RESDSP4
               LOOP  @RESDSP2
               JMP   @RESDSP5
  @RESDSP4:    SUB   DL,$04
               IN    AL,DX
               CMP   AL,$AA
               JZ    @RESDSP6
               DEC   BL
               JNZ   @RESDSP3
  @RESDSP5:    ADD   WORD PTR IOPORT,+$10
               CMP   WORD PTR IOPORT,$0270
               JBE   @RESDSP7
               MOV   WORD PTR IOPORT,$0000
  @RESDSP6:
  END;
  IF IOPORT <> 0 THEN
  BEGIN
    WRITELN ('SoundBlaster found at port ',HEXW(IOPORT),'h.');
  END ELSE
  BEGIN
    WRITELN ('No SoundBlaster detected. Sound output set to PC-speaker.');
  END;
  WRITELN ('Allocating Atom memory.');
  GETMEM (ATOMMEM1,$FFF8);
  GETMEM (ATOMMEM2,$FFF8);
  GETMEM (ATOMMEM3,$0200);
  ATOMMEMSEG := SEG(ATOMMEM1^);
  IF OFS(ATOMMEM1^) <> $0000 THEN INC (ATOMMEMSEG);
  GETMEM (FINBUF,SIZEOF(FINBUFTYPE));
  FINBUFOFS := OFS(FINBUF^);
  FINBUFSEG := SEG(FINBUF^);
  FINSIZE := 0;
  FOUTOPEN := 0;
  GETMEM (FOUTBUF,SIZEOF(FOUTBUFTYPE));
  FOUTBUFOFS := OFS(FOUTBUF^);
  FOUTBUFSEG := SEG(FOUTBUF^);
  ASM;
               CLD
               MOV   WORD PTR [CS:DATASEG],DS
               {---clear extROMmem---}
               SUB   AX,AX
               SUB   DI,DI
               MOV   BX,WORD PTR ATOMMEMSEG
               ADD   BX,$1000
               MOV   ES,BX
               MOV   CX,$8000
               REPZ
               STOSW
               MOV   BX,ES
               ADD   BX,$1000
               MOV   ES,BX
               MOV   CX,$0140/2
               REPZ
               STOSW
               {---clear atom memory---}
               SUB   DI,DI
               MOV   ES,WORD PTR ATOMMEMSEG
               MOV   CX,$8000
               REPZ
               STOSW
               {---store EMU detection---}
               MOV   SI,OFFSET EMUDETECT
               MOV   DI,$BF80
               MOV   CX,+65
               REPZ
               MOVSB
               {---store atom rom memory---}
               MOV   SI,OFFSET ATOMROMMEM
               MOV   DI,$A000
               MOV   CX,$0800
               REPZ
               MOVSW
               MOV   DI,$C000
               MOV   CX,$2000
               REPZ
               MOVSW
               {---store random seed---}
               PUSHF
               PUSHA
               MOV   AH,$2C
               INT   $21
               XOR   CL,CH
               ROL   CL,4
               ADD   DH,CL
               MOV   WORD PTR [ES:$0008],DX
               MOV   AX,DX
               AND   CX,$00FF
               MUL   CX
               MOV   WORD PTR [ES:$000A],AX
               MOV   BYTE PTR [ES:$000C],DL
               POPA
               POPF
               {---make graphtables---}
               SUB   DI,DI
               MOV   BL,$00
  @INIT2:      MOV   AL,BL
               CALL  MAKEWIDER
               MOV   BYTE PTR MONOGRAPHTABLE[DI    ],AH
               MOV   BYTE PTR MONOGRAPHTABLE[DI+$01],$00
               MOV   WORD PTR MONOGRAPHTABLE[DI+$02],$0000
               MOV   BYTE PTR MONOGRAPHTABLE[DI+$04],AL
               MOV   BYTE PTR MONOGRAPHTABLE[DI+$05],$00
               MOV   WORD PTR MONOGRAPHTABLE[DI+$06],$0000
               MOV   BYTE PTR GREYGRAPHTABLE[DI    ],$00
               MOV   BYTE PTR GREYGRAPHTABLE[DI+$01],AH
               MOV   WORD PTR GREYGRAPHTABLE[DI+$02],$0000
               MOV   BYTE PTR GREYGRAPHTABLE[DI+$04],$00
               MOV   BYTE PTR GREYGRAPHTABLE[DI+$05],AL
               MOV   WORD PTR GREYGRAPHTABLE[DI+$06],$0000
               ADD   DI,+$08
               INC   BL
               JNZ   @INIT2
               SUB   DI,DI
               MOV   BL,$00
  @INIT3:      MOV   WORD PTR COLORGRAPHTABLE[DI    ],+$00
               MOV   WORD PTR COLORGRAPHTABLE[DI+$02],+$00
               MOV   WORD PTR COLORGRAPHTABLE[DI+$04],+$00
               MOV   WORD PTR COLORGRAPHTABLE[DI+$06],+$00
               MOV   AL,BL
               MOV   CX,$0004
  @INIT8:      MOV   AH,$00
               SHL   AX,2
               CMP   AH,$00
               JNZ   @INIT4
               OR    BYTE PTR COLORGRAPHTABLE[DI+$04],$0F
               OR    BYTE PTR COLORGRAPHTABLE[DI+$05],$0F
               JMP   @INIT7
  @INIT4:      CMP   AH,$01
               JNZ   @INIT5
               OR    BYTE PTR COLORGRAPHTABLE[DI+$06],$0F
               JMP   @INIT7
  @INIT5:      CMP   AH,$02
               JNZ   @INIT6
               OR    BYTE PTR COLORGRAPHTABLE[DI+$04],$0F
               OR    BYTE PTR COLORGRAPHTABLE[DI+$06],$0F
               JMP   @INIT7
  @INIT6:      OR    BYTE PTR COLORGRAPHTABLE[DI+$05],$0F
               OR    BYTE PTR COLORGRAPHTABLE[DI+$06],$0F
  @INIT7:      CMP   CX,+$01
               JZ    @INIT10
               PUSH  CX
               MOV   CX,$0004
  @INIT9:      SHL   BYTE PTR COLORGRAPHTABLE[DI+$04],1
               RCL   BYTE PTR COLORGRAPHTABLE[DI    ],1
               SHL   BYTE PTR COLORGRAPHTABLE[DI+$05],1
               RCL   BYTE PTR COLORGRAPHTABLE[DI+$01],1
               SHL   BYTE PTR COLORGRAPHTABLE[DI+$06],1
               RCL   BYTE PTR COLORGRAPHTABLE[DI+$02],1
               SHL   BYTE PTR COLORGRAPHTABLE[DI+$07],1
               RCL   BYTE PTR COLORGRAPHTABLE[DI+$03],1
               LOOP  @INIT9
               POP   CX
               LOOP  @INIT8
  @INIT10:     ADD   DI,+$08
               INC   BL
               JNZ   @INIT3
  END;
  FOUTNAME := '';
END;

{---[timer (for determining the CPU speed)]---------------------------------}
PROCEDURE TIMER;
LABEL 1;
VAR P:POINTER;
    POFS,PSEG:WORD;
    T:LONGINT;
    W:WORD;
    I:BYTE;
BEGIN
  IF MEMW[CSEG:OFS(WACHTCONST)] <> 0 THEN
  BEGIN
    W := MEMW[CSEG:OFS(WACHTCONST)];
    GOTO 1;
  END;
  WRITE ('Determining CPU-speed. ');
  GETMEM (P,$FFF8);
  POFS := OFS(P^);
  PSEG := SEG(P^);
  T := 0;
  FOR I := 1 TO 20 DO
  BEGIN
    ASM;
               MOV   DI,WORD PTR POFS
               MOV   WORD PTR @SUBR[$00],DI
               MOV   ES,WORD PTR PSEG
               MOV   WORD PTR @SUBR[$02],ES
               CLD
               MOV   AX,$F8F8
               MOV   CX,$FFF0/2
               REPZ
               STOSW
               MOV   AL,$CB
               STOSB
               NOP
               IN    AL,$61
               PUSH  AX
               CLI
               AND   AL,$FE
               OUT   $61,AL
               MOV   AL,$B2
               OUT   $43,AL
               MOV   AL,$00
               OUT   $42,AL
               OUT   $42,AL
               IN    AL,$61
               OR    AL,$01
               AND   AL,$FD
               OUT   $61,AL
               MOV   CX,$0003
    @TIMER2:   NOP
               DB    $2E,$FF,$1E
               DW    OFFSET @SUBR
               NOP
               LOOP  @TIMER2
               IN    AL,$61
               AND   AL,$FE
               OUT   $61,AL
               MOV   AL,$B0
               OUT   $43,AL
               IN    AL,$42
               MOV   AH,AL
               IN    AL,$42
               XCHG  AL,AH
               NEG   AX
               MOV   WORD PTR W,AX
               POP   AX
               OUT   $61,AL
               STI
               JMP   @TIMER1
    @SUBR:     DD    $00000000
    @TIMER1:
    END;
    INC (T,LONGINT(W));
  END;
  FREEMEM (P,$FFF8);
  T := T DIV 20; {P120: 3839}
  W := 460680 DIV T;
1:ASM;
               MOV   AX,WORD PTR W
               MOV   BX,AX
    @TIMER5:   SUB   BX,+33
               JC    @TIMER4
               INC   AX
               JMP   @TIMER5
    @TIMER4:   MOV   WORD PTR PCWAITTABLE[CS:$0002],AX
               MOV   DI,$0004
               MOV   CX,$0002
    @TIMER3:   MOV   AX,WORD PTR PCWAITTABLE[CS:$0002]
               MUL   CX
               MOV   WORD PTR PCWAITTABLE[CS:DI],AX
               ADD   DI,+$02
               INC   CX
               CMP   CX,+$08
               JBE   @TIMER3
  END;
  WRITELN ('SpeedIndex set to ',MEMW[CSEG:OFS(PCWAITTABLE)+2],'.');
END;

{---[graphmode]-------------------------------------------------------------}
PROCEDURE GRAPHMODE; ASSEMBLER;
ASM;
               DB    $00 {00=0;01=1;02=2;03=3;04=4;05=1a;06=2a;07=3a;08=4a}
END;

{---[programcnt (word)]-----------------------------------------------------}
PROCEDURE PROGRAMCNT; ASSEMBLER;
ASM;
               DB    $00
END;

{---[stackpointer (word)]---------------------------------------------------}
PROCEDURE STACKPOINTER; ASSEMBLER;
ASM;
               DB    $00
END;

{---[accu_b (byte)]---------------------------------------------------------}
PROCEDURE ACCU_B; ASSEMBLER;
ASM;
END;

{---[accumulator (byte)]----------------------------------------------------}
PROCEDURE ACCUMULATOR; ASSEMBLER;
ASM;
END;

{---[flagregister (byte)]---------------------------------------------------}
PROCEDURE FLAGREGISTER; ASSEMBLER;
ASM;
END;

{---[xregister (byte)]------------------------------------------------------}
PROCEDURE XREGISTER; ASSEMBLER;
ASM;
END;

{---[yregister (byte)]------------------------------------------------------}
PROCEDURE YREGISTER; ASSEMBLER;
ASM;
END;

{---[t2l_l (VIA timer 2 low latch register)]--------------------------------}
PROCEDURE T2L_L; ASSEMBLER;
ASM;
END;

{---[mousenr]---------------------------------------------------------------}
PROCEDURE MOUSENR; ASSEMBLER;
ASM;
END;

{---[mousebackgrpos (word)]-------------------------------------------------}
PROCEDURE MOUSEBACKGRPOS; ASSEMBLER;
ASM;
               DB    $00
END;

{---[irqdelay (VIA interrupt delay count)]----------------------------------}
PROCEDURE IRQDELAY; ASSEMBLER;
ASM;
END;

{---[nmidelay]--------------------------------------------------------------}
PROCEDURE NMIDELAY; ASSEMBLER;
ASM;
END;

{---[graphtop (depending on graphics mode)]---------------------------------}
PROCEDURE GRAPHTOP; ASSEMBLER;
ASM;
               DW    $8200
               DW    $8400
               DW    $8600
               DW    $8C00
               DW    $9800
               DW    $8400
               DW    $8800
               DW    $8C00
               DW    $9800
END;

{---[brkpnton (bit 7 reserved for TRACE/STEP/HERE)]-------------------------}
PROCEDURE BRKPNTON; ASSEMBLER;
ASM;
               DB    $00
END;

{---[brkpnts]---------------------------------------------------------------}
PROCEDURE BRKPNTS; ASSEMBLER;
ASM;
               DW    $0000
               DW    $0000
               DW    $0000
               DW    $0000
END;

{---[aantboxret (byte)]-----------------------------------------------------}
PROCEDURE AANTBOXRET; ASSEMBLER; {---max.20h---}
ASM;
               DB    $00
END;

{---[boxreturns]------------------------------------------------------------}
PROCEDURE BOXRETURNS; ASSEMBLER;
ASM;
               DW    $0000,$0000,$0000,$0000
               DW    $0000,$0000,$0000,$0000
               DW    $0000,$0000,$0000,$0000
               DW    $0000,$0000,$0000,$0000

               DW    $0000,$0000,$0000,$0000
               DW    $0000,$0000,$0000,$0000
               DW    $0000,$0000,$0000,$0000
               DW    $0000,$0000,$0000,$0000
END;

{---[boxinfo]---------------------------------------------------------------}
PROCEDURE BOXINFO; ASSEMBLER;
ASM;
               PUSH  DS
               PUSHA
               MOV   BH,BYTE PTR [SCHAKELBYTE]
               AND   BH,$0F
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   BYTE PTR [CS:CURSORX],+9
               MOV   BYTE PTR [CS:CURSORY],+1
               MOV   BL,$09
               MOV   AL,01000101b
               CALL  PRINTCHAR
               MOV   CX,+21
               MOV   AL,01001100b
@BOXINF1:      CALL  PRINTCHAR
               LOOP  @BOXINF1
               MOV   AL,01001010b
               CALL  PRINTCHAR
               MOV   DL,$00
@BOXINF2:      MOV   BYTE PTR [CS:CURSORX],+9
               MOV   AL,DL
               ADD   AL,$02
               MOV   BYTE PTR [CS:CURSORY],AL
               MOV   AL,01010101b
               CALL  PRINTCHAR
               MOV   CX,+21
               MOV   AL,' '
@BOXINF3:      CALL  PRINTCHAR
               LOOP  @BOXINF3
               MOV   AL,01101010b
               CALL  PRINTCHAR
               INC   DL
               CMP   DL,$10
               JB    @BOXINF2
               MOV   BYTE PTR [CS:CURSORX],+9
               MOV   BYTE PTR [CS:CURSORY],+18
               MOV   AL,01010100b
               CALL  PRINTCHAR
               MOV   CX,+21
               MOV   AL,01001100b
@BOXINF8:      CALL  PRINTCHAR
               LOOP  @BOXINF8
               MOV   AL,01101000b
               CALL  PRINTCHAR
               MOV   DL,$00
@BOXINF4:      MOV   BL,$0E
               CMP   BH,DL
               JNZ   @BOXINF7
               MOV   BL,$0F
@BOXINF7:      MOV   BYTE PTR [CS:CURSORX],+11
               MOV   AL,DL
               ADD   AL,$02
               MOV   BYTE PTR [CS:CURSORY],AL
               MOV   AL,DL
               ADD   AL,'0'
               CMP   AL,'9'
               JBE   @BOXINF9
               ADD   AL,$07
               AND   AL,$3F
@BOXINF9:      CALL  PRINTCHAR
               MOV   AL,':'
               CALL  PRINTCHAR
               INC   BYTE PTR [CS:CURSORX]
               MOV   SI,DX
               AND   SI,$000F
               SHL   SI,4
               ADD   SI,OFFSET BOXNAMES
               MOV   CX,$0010
@BOXINF5:      LODSB
               AND   AL,$3F
               JZ    @BOXINF6
               CALL  PRINTCHAR
               LOOP  @BOXINF5
@BOXINF6:      INC   DL
               CMP   DL,$10
               JB    @BOXINF4
               POPA
               POP   DS
END;

{---[atomseg (word)]--------------------------------------------------------}
PROCEDURE ATOMSEG; ASSEMBLER;
ASM;
               DB    $00
END;

{---[tapescreen (byte)]-----------------------------------------------------}
PROCEDURE TAPESCREEN; ASSEMBLER;
ASM;
               DB    $00
END;

{---[putbyte_part2]---------------------------------------------------------}
PROCEDURE PUTBYTE_PART2; ASSEMBLER;
ASM;
               TEST  BYTE PTR [CS:MOUSENR],$80
               JNZ   @PUTBYTE1
               MOV   AX,DI
               SUB   AX,WORD PTR [CS:MOUSEBACKGRPOS]
               JC    @PUTBYTE1
               CMP   AX,$07F0
               JAE   @PUTBYTE1
               MOV   BX,AX
               SHR   AX,4
               PUSH  CX
               MOV   CL,$12
               DIV   CL
               POP   CX
               OR    AH,AH
               JNZ   @PUTBYTE1
               {---under mousecursor---}
               AND   BX,$0008
               SHL   AX,4
               ADD   BX,AX
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR [SI]
               MOV   WORD PTR MOUSEBACKGROUND[BX],AX
               OR    AX,WORD PTR MOUSEPOINTER[BX]
               MOV   WORD PTR [ES:DI],AX
               MOV   AX,WORD PTR [SI+2]
               MOV   WORD PTR MOUSEBACKGROUND[BX+2],AX
               OR    AX,WORD PTR MOUSEPOINTER[BX+2]
               MOV   WORD PTR [ES:DI+2],AX
               MOV   AX,WORD PTR [SI+4]
               MOV   WORD PTR MOUSEBACKGROUND[BX+4],AX
               OR    AX,WORD PTR MOUSEPOINTER[BX+4]
               MOV   WORD PTR [ES:DI+4],AX
               MOV   AX,WORD PTR [SI+6]
               MOV   WORD PTR MOUSEBACKGROUND[BX+6],AX
               OR    AX,WORD PTR MOUSEPOINTER[BX+6]
               MOV   WORD PTR [ES:DI+6],AX
               RETN
@PUTBYTE1:     MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR [SI]
               MOV   WORD PTR [ES:DI],AX
               MOV   AX,WORD PTR [SI+2]
               MOV   WORD PTR [ES:DI+2],AX
               MOV   AX,WORD PTR [SI+4]
               MOV   WORD PTR [ES:DI+4],AX
               MOV   AX,WORD PTR [SI+6]
               MOV   WORD PTR [ES:DI+6],AX
END;

{---[putmode0byte; AL=byte; AH=00:white/01:grey; DI=screenpos]--------------}
PROCEDURE PUTMODE0BYTE; ASSEMBLER;
ASM;
@PUTMODE0BYTE: PUSH  DS
               PUSH  SI
               PUSH  BX
               PUSH  DI
               PUSH  AX
               MOV   SI,AX
               AND   SI,$00FF
               SHL   SI,3
               OR    AH,AH
               JNZ   @PUTMODE0_1
               ADD   SI,OFFSET MONOGRAPHTABLE
               JMP   @PUTMODE0_2
@PUTMODE0_1:   ADD   SI,OFFSET GREYGRAPHTABLE
@PUTMODE0_2:   CALL  PUTBYTE_PART2
               POP   AX
               POP   DI
               POP   BX
               POP   SI
               POP   DS
END;

{---[putmonobyte; AL=byte; DI=screenpos]------------------------------------}
PROCEDURE PUTMONOBYTE; ASSEMBLER;
ASM;
               PUSH  DS
               PUSH  SI
               PUSH  BX
               PUSH  DI
               PUSH  AX
               MOV   SI,AX
               AND   SI,$00FF
               SHL   SI,3
               ADD   SI,OFFSET MONOGRAPHTABLE
               CALL  PUTBYTE_PART2
               POP   AX
               POP   DI
               POP   BX
               POP   SI
               POP   DS
END;

{---[putmonoword; AX=word; DI=screenpos]------------------------------------}
PROCEDURE PUTMONOWORD; ASSEMBLER;
ASM;
               PUSH  DS
               PUSH  SI
               PUSH  BX
               PUSH  DI
               PUSH  AX
               MOV   SI,AX
               AND   SI,$00FF
               SHL   SI,3
               ADD   SI,OFFSET MONOGRAPHTABLE
               CALL  PUTBYTE_PART2
               POP   AX
               POP   DI
               PUSH  DI
               PUSH  AX
               ADD   DI,+$08
               MOV   AL,AH
               MOV   SI,AX
               AND   SI,$00FF
               SHL   SI,3
               ADD   SI,OFFSET MONOGRAPHTABLE
               CALL  PUTBYTE_PART2
               POP   AX
               POP   DI
               POP   BX
               POP   SI
               POP   DS
END;

{---[putcolorbyte; AL=byte; DI=screenpos]-----------------------------------}
PROCEDURE PUTCOLORBYTE; ASSEMBLER;
ASM;
               PUSH  DS
               PUSH  SI
               PUSH  BX
               PUSH  DI
               PUSH  AX
               MOV   SI,AX
               AND   SI,$00FF
               SHL   SI,3
               ADD   SI,OFFSET COLORGRAPHTABLE
               CALL  PUTBYTE_PART2
               POP   AX
               POP   DI
               POP   BX
               POP   SI
               POP   DS
END;

{---[putcolorword; AX=word; DI=screenpos]-----------------------------------}
PROCEDURE PUTCOLORWORD; ASSEMBLER;
ASM;
               PUSH  DS
               PUSH  SI
               PUSH  BX
               PUSH  DI
               PUSH  AX
               MOV   SI,AX
               AND   SI,$00FF
               SHL   SI,3
               ADD   SI,OFFSET COLORGRAPHTABLE
               CALL  PUTBYTE_PART2
               POP   AX
               POP   DI
               PUSH  DI
               PUSH  AX
               ADD   DI,+$08
               MOV   AL,AH
               MOV   SI,AX
               AND   SI,$00FF
               SHL   SI,3
               ADD   SI,OFFSET COLORGRAPHTABLE
               CALL  PUTBYTE_PART2
               POP   AX
               POP   DI
               POP   BX
               POP   SI
               POP   DS
END;

{---[updatem0]--------------------------------------------------------------}
PROCEDURE UPDATEM0; ASSEMBLER;
ASM;
               PUSHF
               ADD   WORD PTR [PCCYCLES],+750
               CLI
               PUSH  DS
               PUSH  SI
               MOV   AH,$00
               MOV   AL,BYTE PTR [DI]
               CMP   AL,$C0
               JB    @UPDM0_1
               {---grey graphics symbols---}
               AND   AL,$7F
               MOV   AH,$01
@UPDM0_1:      PUSH  AX
               PUSH  AX
               MOV   AX,DI
               PUSH  AX
               AND   AX,$01E0
               SHL   AX,2
               MOV   DI,AX
               SHL   AX,1
               ADD   DI,AX
               SHL   AX,2
               ADD   DI,AX
               SHL   AX,1
               ADD   DI,AX
               POP   AX
               AND   AX,$001F
               SHL   AX,3
               ADD   AX,$0140
               ADD   DI,AX
               POP   AX
               MOV   AH,$00
               SHL   AX,4
               ADD   AX,OFFSET CHARDATA
               MOV   SI,AX
               MOV   DS,WORD PTR [CS:DATASEG]
               POP   AX
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CALL  PUTMODE0BYTE
               ADD   DI,$0120
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CALL  PUTMODE0BYTE
               ADD   DI,$0120
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CALL  PUTMODE0BYTE
               ADD   DI,$0120
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CALL  PUTMODE0BYTE
               ADD   DI,$0120
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CALL  PUTMODE0BYTE
               ADD   DI,$0120
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CALL  PUTMODE0BYTE
               ADD   DI,$0120
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CALL  PUTMODE0BYTE
               ADD   DI,$0120
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CALL  PUTMODE0BYTE
               ADD   DI,$0120
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CALL  PUTMODE0BYTE
               ADD   DI,$0120
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CALL  PUTMODE0BYTE
               ADD   DI,$0120
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CALL  PUTMODE0BYTE
               ADD   DI,$0120
               MOV   AL,BYTE PTR [SI]
               CALL  PUTMODE0BYTE
               POP   SI
               POP   DS
               POPF
END;

{---[updatem1]--------------------------------------------------------------}
PROCEDURE UPDATEM1; ASSEMBLER;
ASM;
               PUSHF
               CLI
               ADD   WORD PTR [PCCYCLES],+337
               PUSH  BX
               MOV   BL,BYTE PTR [DI]
               PUSH  DI
               AND   DI,$03F0
               SHL   DI,1
               MOV   AX,DI
               SHL   AX,1
               ADD   DI,AX
               SHL   AX,2
               ADD   DI,AX
               SHL   AX,1
               ADD   DI,AX
               POP   AX
               AND   AX,$000F
               SHL   AX,4
               ADD   AX,$0140
               ADD   DI,AX
               MOV   BH,$00
               SHL   BX,1
               MOV   AX,WORD PTR WIDERTABLE[CS:BX]
               CALL  PUTMONOWORD
               ADD   DI,$0120
               CALL  PUTMONOWORD
               ADD   DI,$0120
               CALL  PUTMONOWORD
               POP   BX
               POPF
END;

{---[updatem1a]-------------------------------------------------------------}
PROCEDURE UPDATEM1a; ASSEMBLER;
ASM;
               PUSHF
               CLI
               ADD   WORD PTR [PCCYCLES],+310
               PUSH  BX
               MOV   BL,BYTE PTR [DI]
               PUSH  DI
               AND   DI,$03F0
               SHL   DI,1
               MOV   AX,DI
               SHL   AX,1
               ADD   DI,AX
               SHL   AX,2
               ADD   DI,AX
               SHL   AX,1
               ADD   DI,AX
               POP   AX
               AND   AX,$000F
               SHL   AX,4
               ADD   AX,$0140
               ADD   DI,AX
               MOV   BH,$00
               SHL   BX,1
               MOV   AX,WORD PTR WIDER1aTABLE[CS:BX]
               CALL  PUTCOLORWORD
               ADD   DI,$0120
               CALL  PUTCOLORWORD
               ADD   DI,$0120
               CALL  PUTCOLORWORD
               POP   BX
               POPF
END;

{---[updatem2]--------------------------------------------------------------}
PROCEDURE UPDATEM2; ASSEMBLER;
ASM;
               PUSHF
               CLI
               ADD   WORD PTR [PCCYCLES],+254
               PUSH  BX
               MOV   BL,BYTE PTR [DI]
               PUSH  DI
               AND   DI,$0FF0
               SHL   DI,2
               MOV   AX,DI
               SHL   AX,3
               ADD   DI,AX
               POP   AX
               AND   AX,$000F
               SHL   AX,4
               ADD   AX,$0140
               ADD   DI,AX
               MOV   BH,$00
               SHL   BX,1
               MOV   AX,WORD PTR WIDERTABLE[CS:BX]
               CALL  PUTMONOWORD
               ADD   DI,$0120
               CALL  PUTMONOWORD
               POP   BX
               POPF
END;

{---[updatem2a]-------------------------------------------------------------}
PROCEDURE UPDATEM2a; ASSEMBLER;
ASM;
               PUSHF
               CLI
               ADD   WORD PTR [PCCYCLES],+217
               MOV   AL,BYTE PTR [DI]
               PUSH  AX
               PUSH  DI
               AND   DI,$07E0
               MOV   AX,DI
               SHL   AX,1
               ADD   DI,AX
               SHL   AX,2
               ADD   DI,AX
               SHL   AX,1
               ADD   DI,AX
               POP   AX
               AND   AX,$001F
               SHL   AX,3
               ADD   AX,$0140
               ADD   DI,AX
               POP   AX
               CALL  PUTCOLORBYTE
               ADD   DI,$0120
               CALL  PUTCOLORBYTE
               ADD   DI,$0120
               CALL  PUTCOLORBYTE
               POPF
END;

{---[updatem3]--------------------------------------------------------------}
PROCEDURE UPDATEM3; ASSEMBLER;
ASM;
               PUSHF
               CLI
               ADD   WORD PTR [PCCYCLES],+178
               PUSH  BX
               MOV   BL,BYTE PTR [DI]
               PUSH  DI
               AND   DI,$0FF0
               SHL   DI,1
               MOV   AX,DI
               SHL   AX,3
               ADD   DI,AX
               POP   AX
               AND   AX,$000F
               SHL   AX,4
               ADD   AX,$0140
               ADD   DI,AX
               MOV   BH,$00
               SHL   BX,1
               MOV   AX,WORD PTR WIDERTABLE[CS:BX]
               CALL  PUTMONOWORD
               POP   BX
               POPF
END;

{---[updatem3a]-------------------------------------------------------------}
PROCEDURE UPDATEM3a; ASSEMBLER;
ASM;
               PUSHF
               CLI
               ADD   WORD PTR [PCCYCLES],+177
               MOV   AL,BYTE PTR [DI]
               PUSH  AX
               PUSH  DI
               AND   DI,$0FE0
               SHL   DI,1
               MOV   AX,DI
               SHL   AX,3
               ADD   DI,AX
               POP   AX
               AND   AX,$001F
               SHL   AX,3
               ADD   AX,$0140
               ADD   DI,AX
               POP   AX
               CALL  PUTCOLORBYTE
               ADD   DI,$0120
               CALL  PUTCOLORBYTE
               POPF
END;

{---[updatem4]--------------------------------------------------------------}
PROCEDURE UPDATEM4; ASSEMBLER;
ASM;
               PUSHF
               CLI
               ADD   WORD PTR [PCCYCLES],+139
               MOV   AL,BYTE PTR [DI]
               PUSH  AX
               PUSH  DI
               AND   DI,$1FE0
               MOV   AX,DI
               SHL   AX,3
               ADD   DI,AX
               POP   AX
               AND   AX,$001F
               SHL   AX,3
               ADD   AX,$0140
               ADD   DI,AX
               POP   AX
               CALL  PUTMONOBYTE
               POPF
END;

{---[updatem4a]-------------------------------------------------------------}
PROCEDURE UPDATEM4a; ASSEMBLER;
ASM;
               PUSHF
               CLI
               ADD   WORD PTR [PCCYCLES],+134
               MOV   AL,BYTE PTR [DI]
               PUSH  AX
               PUSH  DI
               AND   DI,$1FE0
               MOV   AX,DI
               SHL   AX,3
               ADD   DI,AX
               POP   AX
               AND   AX,$001F
               SHL   AX,3
               ADD   AX,$0140
               ADD   DI,AX
               POP   AX
               CALL  PUTCOLORBYTE
               POPF
END;

{---[updatetable]-----------------------------------------------------------}
PROCEDURE UPDATETABLE; ASSEMBLER;
ASM;
               DW    OFFSET UPDATEM0
               DW    OFFSET UPDATEM1
               DW    OFFSET UPDATEM2
               DW    OFFSET UPDATEM3
               DW    OFFSET UPDATEM4
               DW    OFFSET UPDATEM1a
               DW    OFFSET UPDATEM2a
               DW    OFFSET UPDATEM3a
               DW    OFFSET UPDATEM4a
END;

{---[updategraph DI=dest.address]-------------------------------------------}
PROCEDURE UPDATEGRAPH; ASSEMBLER;
ASM;
               PUSHF
               CMP   DI,$8000
               JAE   @UPDATEG1
               ADD   WORD PTR [PCCYCLES],+21
               POPF
               RETN
@UPDATEG1:     PUSH  BX
               MOV   BL,BYTE PTR [CS:GRAPHMODE]
               MOV   BH,$00
               SHL   BX,1
               CMP   DI,WORD PTR GRAPHTOP[CS:BX]
               JB    @UPDATEG2
               POP   BX
               ADD   WORD PTR [PCCYCLES],+40
               POPF
               RETN
@UPDATEG2:     MOV   AX,WORD PTR UPDATETABLE[CS:BX]
               POP   BX
               POPF
               JMP   AX
END;

{---[setmousecursor (AL=waarde)]--------------------------------------------}
PROCEDURE SETMOUSECURSOR; ASSEMBLER;
ASM;
               TEST  BYTE PTR [CS:MOUSENR],$80
               JNZ   @SETMOUSE2
@SETMOUSE3:    RETN
@SETMOUSE2:    OR    AL,AL
               JS    @SETMOUSE3
               MOV   BYTE PTR [CS:MOUSENR],AL
               PUSH  DS
               PUSHA
               MOV   DS,WORD PTR [CS:ATOMSEG]
               MOV   AL,+255
               SUB   AL,BYTE PTR [$BFE1]
               MOV   AH,$00
               SHL   AX,5
               MOV   DI,AX
               SHL   AX,3
               ADD   DI,AX
               MOV   AL,BYTE PTR [$BFE0]
               MOV   CL,AL
               AND   CL,$07
               AND   AX,$00F8
               ADD   DI,AX
               ADD   DI,$0140
               MOV   AL,BYTE PTR [CS:MOUSENR]
               AND   AX,$001F
               SHL   AX,3
               MOV   SI,AX
               SUB   BX,BX
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   WORD PTR [CS:MOUSEBACKGRPOS],DI
@SETMOUSE1:    MOV   AH,BYTE PTR MOUSECURSORS[CS:SI]
               MOV   AL,$00
               SHR   AX,CL
               XCHG  AL,AH
               PUSH  SI
               PUSH  AX
               MOV   AX,WORD PTR [ES:DI]
               MOV   WORD PTR MOUSEBACKGROUND[BX],AX
               MOV   AX,WORD PTR [ES:DI+2]
               MOV   WORD PTR MOUSEBACKGROUND[BX+2],AX
               MOV   AX,WORD PTR [ES:DI+4]
               MOV   WORD PTR MOUSEBACKGROUND[BX+4],AX
               MOV   AX,WORD PTR [ES:DI+6]
               MOV   WORD PTR MOUSEBACKGROUND[BX+6],AX
               MOV   AX,WORD PTR [ES:DI+8]
               MOV   WORD PTR MOUSEBACKGROUND[BX+8],AX
               MOV   AX,WORD PTR [ES:DI+10]
               MOV   WORD PTR MOUSEBACKGROUND[BX+10],AX
               MOV   AX,WORD PTR [ES:DI+12]
               MOV   WORD PTR MOUSEBACKGROUND[BX+12],AX
               MOV   AX,WORD PTR [ES:DI+14]
               MOV   WORD PTR MOUSEBACKGROUND[BX+14],AX
               POP   AX
               MOV   SI,AX
               AND   SI,$00FF
               SHL   SI,3
               ADD   SI,OFFSET MONOGRAPHTABLE
               PUSH  AX
               MOV   AL,BYTE PTR [SI]
               MOV   AH,AL
               MOV   WORD PTR MOUSEPOINTER[BX],AX
               OR    WORD PTR [ES:DI],AX
               MOV   WORD PTR MOUSEPOINTER[BX+2],AX
               OR    WORD PTR [ES:DI+2],AX
               MOV   AL,BYTE PTR [SI+4]
               MOV   AH,AL
               MOV   WORD PTR MOUSEPOINTER[BX+4],AX
               OR    WORD PTR [ES:DI+4],AX
               MOV   WORD PTR MOUSEPOINTER[BX+6],AX
               OR    WORD PTR [ES:DI+6],AX
               POP   AX
               XCHG  AL,AH
               MOV   SI,AX
               AND   SI,$00FF
               SHL   SI,3
               ADD   SI,OFFSET MONOGRAPHTABLE
               MOV   AL,BYTE PTR [SI]
               MOV   AH,AL
               MOV   WORD PTR MOUSEPOINTER[BX+8],AX
               OR    WORD PTR [ES:DI+8],AX
               MOV   WORD PTR MOUSEPOINTER[BX+10],AX
               OR    WORD PTR [ES:DI+10],AX
               MOV   AL,BYTE PTR [SI+4]
               MOV   AH,AL
               MOV   WORD PTR MOUSEPOINTER[BX+12],AX
               OR    WORD PTR [ES:DI+12],AX
               MOV   WORD PTR MOUSEPOINTER[BX+14],AX
               OR    WORD PTR [ES:DI+14],AX
               POP   SI
               ADD   BX,+16
               ADD   DI,$0120
               INC   SI
               TEST  SI,$0007
               JNZ   @SETMOUSE1
               POPA
               POP   DS
END;

{---[clrmousecursor]--------------------------------------------------------}
PROCEDURE CLRMOUSECURSOR; ASSEMBLER;
ASM;
               TEST  BYTE PTR [CS:MOUSENR],$80
               JZ    @CLRMOUSE2
               RETN
@CLRMOUSE2:    OR    BYTE PTR [CS:MOUSENR],$80
               PUSH  DS
               PUSHA
               MOV   DS,WORD PTR [CS:ATOMSEG]
               MOV   AL,+255
               SUB   AL,BYTE PTR [$BFE1]
               MOV   AH,$00
               SHL   AX,5
               MOV   DI,AX
               SHL   AX,3
               ADD   DI,AX
               MOV   AL,BYTE PTR [$BFE0]
               AND   AX,$00F8
               ADD   DI,AX
               ADD   DI,$0140
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   SI,OFFSET MOUSEBACKGROUND
               MOV   CX,$0008
@CLRMOUSE1:    MOV   AX,WORD PTR [SI]
               MOV   WORD PTR [ES:DI],AX
               MOV   AX,WORD PTR [SI+2]
               MOV   WORD PTR [ES:DI+2],AX
               MOV   AX,WORD PTR [SI+4]
               MOV   WORD PTR [ES:DI+4],AX
               MOV   AX,WORD PTR [SI+6]
               MOV   WORD PTR [ES:DI+6],AX
               MOV   AX,WORD PTR [SI+8]
               MOV   WORD PTR [ES:DI+8],AX
               MOV   AX,WORD PTR [SI+10]
               MOV   WORD PTR [ES:DI+10],AX
               MOV   AX,WORD PTR [SI+12]
               MOV   WORD PTR [ES:DI+12],AX
               MOV   AX,WORD PTR [SI+14]
               MOV   WORD PTR [ES:DI+14],AX
               ADD   SI,+16
               ADD   DI,$0120
               LOOP  @CLRMOUSE1
               POPA
               POP   DS
END;

{---[disablemouse (called whenever desktop opened)]-------------------------}
PROCEDURE DISABLEMOUSE; ASSEMBLER;
ASM;
               PUSH  DS
               PUSH  ES
               PUSHA
               MOV   DS,WORD PTR [CS:ATOMSEG]
               MOV   ES,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR [$BFE0]
               MOV   WORD PTR TEMPMOUSEDAT[ES:$00],AX
               MOV   AL,BYTE PTR [CS:MOUSENR]
               MOV   BYTE PTR TEMPMOUSEDAT[ES:$02],AL
               MOV   AX,$0003
               INT   $33
               MOV   WORD PTR TEMPMOUSEDAT[ES:$03],CX
               MOV   WORD PTR TEMPMOUSEDAT[ES:$05],DX
               POPA
               POP   ES
               POP   DS
               CALL  CLRMOUSECURSOR
END;

{---[enablemouse (called when resuming emulation)]--------------------------}
PROCEDURE ENABLEMOUSE; ASSEMBLER;
ASM;
               PUSH  DS
               PUSH  ES
               PUSHA
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   ES,WORD PTR [CS:ATOMSEG]
               MOV   AX,WORD PTR TEMPMOUSEDAT[$00]
               MOV   WORD PTR [ES:$BFE0],AX
               MOV   AL,BYTE PTR TEMPMOUSEDAT[$02]
               MOV   BYTE PTR [CS:MOUSENR],AL
               MOV   AX,$0004
               MOV   CX,WORD PTR TEMPMOUSEDAT[$03]
               MOV   DX,WORD PTR TEMPMOUSEDAT[$05]
               INT   $33
               MOV   AX,$0003
               INT   $33
               XOR   BL,$07
               MOV   BYTE PTR [ES:$BFE2],BL
               POPA
               POP   ES
               POP   DS
               TEST  BYTE PTR [CS:MOUSENR],$80
               JNZ   @ENABLE1
               MOV   AL,BYTE PTR [CS:MOUSENR]
               OR    BYTE PTR [CS:MOUSENR],$80
               CALL  SETMOUSECURSOR
@ENABLE1:
END;

{---[savezp90]--------------------------------------------------------------}
PROCEDURE SAVEZP90; ASSEMBLER;
ASM;
               TEST  BYTE PTR [CS:BOXSWITCH],$FF
               JZ    @SAVEZP1
               PUSH  ES
               PUSH  BX
               PUSH  SI
               MOV   AX,DS
               ADD   AX,$2000
               MOV   ES,AX
               MOV   AL,BYTE PTR [SCHAKELBYTE]
               AND   AX,$000F
               SHL   AX,4
               MOV   SI,AX
               SUB   BX,BX
@SAVEZP2:      MOV   AX,WORD PTR [BX+$0090]
               MOV   WORD PTR [ES:SI+BX],AX
               ADD   BL,$02
               CMP   BL,$0A
               JB    @SAVEZP2
               SUB   BX,BX
@SAVEZP4:      MOV   AX,WORD PTR [BX+$0200]
               PUSH  AX
               AND   AH,$F0
               CMP   AH,$A0
               POP   AX
               JNZ   @SAVEZP3
               CMP   AX,WORD PTR [ES:BX+$0100]
               JZ    @SAVEZP3
               MOV   WORD PTR [ES:BX+$0100],AX
               MOV   AL,BYTE PTR [SCHAKELBYTE]
               AND   AX,$000F
               MOV   WORD PTR [ES:BX+$0120],AX
@SAVEZP3:      ADD   BL,$02
               CMP   BL,$1C
               JB    @SAVEZP4
               MOV   AX,WORD PTR [$03FE]
               MOV   BL,AH
               AND   BL,$F0
               CMP   BL,$A0
               JNZ   @SAVEZP5
               CMP   AX,WORD PTR [ES:$011C]
               JZ    @SAVEZP5
               MOV   WORD PTR [ES:$011C],AX
               MOV   AL,BYTE PTR [SCHAKELBYTE]
               AND   AX,$000F
               MOV   WORD PTR [ES:$013C],AX
@SAVEZP5:      POP   SI
               POP   BX
               POP   ES
@SAVEZP1:
END;

{---[setA000mem]------------------------------------------------------------}
PROCEDURE SETA000MEM; ASSEMBLER;
ASM;
               TEST  BYTE PTR [CS:BOXSWITCH],$FF
               JZ    @SETA000_1
               PUSH  DS
               PUSH  ES
               PUSH  BX
               PUSH  CX
               PUSH  SI
               MOV   AH,BYTE PTR [SCHAKELBYTE]
               AND   AX,$0F00
               SHL   AH,4
               MOV   SI,AX
               MOV   DI,$A000
               MOV   AX,DS
               MOV   ES,AX
               ADD   AX,$1000
               MOV   DS,AX
               MOV   CX,$0800
               REPZ
               MOVSW
               MOV   AL,BYTE PTR [ES:SCHAKELBYTE]
               AND   AX,$000F
               SHL   AX,4
               MOV   SI,AX
               MOV   AX,DS
               ADD   AX,$1000
               MOV   DS,AX
               SUB   BX,BX
@SETA000_2:    MOV   AX,WORD PTR [SI+BX]
               MOV   WORD PTR [ES:BX+$0090],AX
               ADD   BL,$02
               CMP   BL,$0A
               JB    @SETA000_2
               POP   SI
               POP   CX
               POP   BX
               POP   ES
               POP   DS
@SETA000_1:
END;

{---[setbordercol]----------------------------------------------------------}
PROCEDURE SETBORDERCOL; ASSEMBLER;
ASM;
               MOV   AL,BYTE PTR [CS:GRAPHMODE]
               OR    AL,AL
               JZ    @BORDERCOL1
               CMP   AL,$05
               JAE   @BORDERCOL2
               {---hires mode---}
               MOV   AL,BYTE PTR EMULCOLORS[CS:(1*3)]
               MOV   BYTE PTR EMULCOLORS[CS:(7*3)],AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(1*3+1)]
               MOV   BYTE PTR EMULCOLORS[CS:(7*3+1)],AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(1*3+2)]
               MOV   BYTE PTR EMULCOLORS[CS:(7*3+2)],AL
               TEST  BYTE PTR [$B002],$08
               JZ    @BORDERCOL3
               PUSH  DX
               CLI
               MOV   DX,$03C8
               MOV   AL,$07
               OUT   DX,AL
               INC   DX
               MOV   AL,BYTE PTR INTENSMONO[CS:$00]
               OUT   DX,AL
               MOV   AL,BYTE PTR INTENSMONO[CS:$01]
               OUT   DX,AL
               MOV   AL,BYTE PTR INTENSMONO[CS:$02]
               OUT   DX,AL
               STI
               POP   DX
               RETN
@BORDERCOL1:   {---lores mode---}
               MOV   AL,BYTE PTR EMULCOLORS[CS:(0*3)]
               MOV   BYTE PTR EMULCOLORS[CS:(7*3)],AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(0*3+1)]
               MOV   BYTE PTR EMULCOLORS[CS:(7*3+1)],AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(0*3+2)]
               MOV   BYTE PTR EMULCOLORS[CS:(7*3+2)],AL
@BORDERCOL3:   PUSH  DX
               CLI
               MOV   DX,$03C8
               MOV   AL,$07
               OUT   DX,AL
               INC   DX
               MOV   AL,BYTE PTR EMULCOLORS[CS:(7*3)]
               OUT   DX,AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(7*3+1)]
               OUT   DX,AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(7*3+2)]
               OUT   DX,AL
               STI
               POP   DX
               RETN
@BORDERCOL2:   {---hires colour mode---}
               MOV   AL,BYTE PTR EMULCOLORS[CS:(3*3)]
               MOV   BYTE PTR EMULCOLORS[CS:(7*3)],AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(3*3+1)]
               MOV   BYTE PTR EMULCOLORS[CS:(7*3+1)],AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(3*3+2)]
               MOV   BYTE PTR EMULCOLORS[CS:(7*3+2)],AL
               TEST  BYTE PTR [$B002],$08
               JZ    @BORDERCOL3
               PUSH  DX
               CLI
               MOV   DX,$03C8
               MOV   AL,$07
               OUT   DX,AL
               INC   DX
               MOV   AL,BYTE PTR INTENSCOLOR[CS:$00]
               OUT   DX,AL
               MOV   AL,BYTE PTR INTENSCOLOR[CS:$01]
               OUT   DX,AL
               MOV   AL,BYTE PTR INTENSCOLOR[CS:$02]
               OUT   DX,AL
               STI
               POP   DX
END;

{---[setintenscol]----------------------------------------------------------}
PROCEDURE SETINTENSCOL; ASSEMBLER;
ASM;
               PUSHA
               SUB   BX,BX
@SETINT2:      MOV   AL,BYTE PTR EMULCOLORS[CS:BX+$03]
               MOV   AH,AL
               SHR   AH,1
               ADD   AL,AH
               CMP   AL,$3F
               JBE   @SETINT1
               MOV   AL,$3F
@SETINT1:      MOV   BYTE PTR INTENSMONO[CS:BX],AL
               INC   BL
               CMP   BL,$02
               JBE   @SETINT2
               SUB   BX,BX
@SETINT4:      MOV   AL,BYTE PTR EMULCOLORS[CS:BX+$09]
               MOV   AH,AL
               SHR   AH,1
               ADD   AL,AH
               CMP   AL,$3F
               JBE   @SETINT3
               MOV   AL,$3F
@SETINT3:      MOV   BYTE PTR INTENSCOLOR[CS:BX],AL
               INC   BL
               CMP   BL,$02
               JBE   @SETINT4
               POPA
END;

{---[sortimp]---------------------------------------------------------------}
PROCEDURE SORTIMP (VAR A:ATMFILETYPE; LO,HI:INTEGER);
VAR X,Y:ATMFILEREC;

  PROCEDURE SORTEER (L,R:INTEGER);
  VAR I,J:INTEGER;
  BEGIN
    I := L;
    J := R;
    X := A[(L+R) DIV 2];
    REPEAT
      WHILE A[I].ATMNAME < X.ATMNAME DO INC (I);
      WHILE X.ATMNAME < A[J].ATMNAME DO DEC (J);
      IF I <= J THEN
      BEGIN
        Y := A[I];
        A[I] := A[J];
        A[J] := Y;
        INC (I);
        DEC (J);
      END;
    UNTIL I > J;
    IF L < J THEN SORTEER (L,J);
    IF I < R THEN SORTEER (I,R);
  END;

BEGIN
  SORTEER (LO,HI);
END;

{---[readimportablefiles]---------------------------------------------------}
PROCEDURE READIMPORTABLEFILES;
VAR D:SEARCHREC;
    F:FILE;
    NR:WORD;
    DUMMY:INTEGER;
BEGIN
  AANTALIMPFILES := 0;
  FINDFIRST ('*.ATM',ANYFILE,D);
  WHILE (DOSERROR = 0) AND (AANTALIMPFILES < MAXAANTFILES) DO
  BEGIN
    IF D.ATTR AND $18 = $00 THEN
    BEGIN
      DUMMY := IORESULT;
      ASSIGN (F,D.NAME);
      RESET (F,1);
      BLOCKREAD (F,IMPFILES[AANTALIMPFILES],SIZEOF(ATMFILEREC),NR);
      CLOSE (F);
      FOR NR := 0 TO 15 DO IMPFILES[AANTALIMPFILES].ATMNAME[NR] := #$00;
      FOR NR := 1 TO LENGTH(D.NAME) DO
        IMPFILES[AANTALIMPFILES].ATMNAME[PRED(NR)] := D.NAME[NR];
      INC (AANTALIMPFILES);
    END;
    FINDNEXT (D);
  END;
  IF AANTALIMPFILES > 0 THEN SORTIMP (IMPFILES,0,PRED(AANTALIMPFILES));
END;

{---[load]------------------------------------------------------------------}
PROCEDURE LOAD (TABLEOFS:WORD; FILEPOINTER:INTEGER; VAR NEWFP:WORD);
LABEL 1;
CONST BUFSIZE = $FFF8;
VAR FROMF     : FILE;
    TAPESIZE  : LONGINT;
    FILENAME  : STRING[16];
    CURNAME   : STRING[16];
    W,I,NR    : WORD;
    ATMHEADER : ATMFILEREC;
    STARTADRS : WORD;
    DEST      : POINTER;
    FPOS      : LONGINT;
    INITPOS   : LONGINT;
    BUF       : POINTER;
    BUFSEG    : WORD;
    DUMMY     : INTEGER;
    FRZVERSION: WORD;
BEGIN
  ASM;
               PUSH  DS
               MOV   DS,WORD PTR ATOMMEMSEG
               CALL  SAVEZP90
               POP   DS
  END;
  IF LENGTH(TAPEIMAGENAME) = 0 THEN
  BEGIN
    NEWFP := $8000; {---no tape image selected---}
    EXIT;
  END;
  W := MEMW[ATOMMEMSEG:TABLEOFS];
  FILENAME := '';
  I := 0;
  WHILE (I < 16) AND (MEM[ATOMMEMSEG:W+I] <> $0D) DO
  BEGIN
    FILENAME := FILENAME + CHR(MEM[ATOMMEMSEG:W+I]);
    INC(I);
  END;
  IF LENGTH(FILENAME) = 0 THEN FILENAME := '*';
  DUMMY := IORESULT;
  ASSIGN (FROMF,TAPEIMAGENAME+'.TAP');
  RESET (FROMF,1);
  IF IORESULT <> 0 THEN
  BEGIN
    NEWFP := $8000; {---tape image not found---}
    EXIT;
  END;
  TAPESIZE := FILESIZE(FROMF);
  NEWFP := 0;
  FPOS := 0;
  WHILE (FPOS < TAPESIZE) AND (FILEPOINTER > 0) DO
  BEGIN
    ATMHEADER := ATOMFILES[NEWFP];
    INC (FPOS,SIZEOF(ATMHEADER)+LONGINT(ATMHEADER.DATASIZE));
    DEC (FILEPOINTER);
    INC (NEWFP);
  END;
  INITPOS := FPOS;
  IF INITPOS = 0 THEN INITPOS := TAPESIZE;
1:IF FPOS >= TAPESIZE THEN
  BEGIN
    NEWFP := 0;
    FPOS := 0;
  END;
  ATMHEADER := ATOMFILES[NEWFP];
  INC (FPOS,SIZEOF(ATMHEADER));
  CURNAME := '';
  I := 0;
  WHILE (I < 16) AND (ATMHEADER.ATMNAME[I] <> #$00) DO
  BEGIN
    CURNAME := CURNAME + ATMHEADER.ATMNAME[I];
    INC (I);
  END;
  IF (FILENAME[LENGTH(FILENAME)] = '*') THEN
  BEGIN
    IF (LENGTH(FILENAME) = 1) OR
       (COPY(FILENAME,1,PRED(LENGTH(FILENAME))) =
        COPY (CURNAME,1,PRED(LENGTH(FILENAME)))) THEN FILENAME := CURNAME;
  END;
  IF FILENAME <> CURNAME THEN
  BEGIN
    INC (NEWFP);
    INC (FPOS,LONGINT(ATMHEADER.DATASIZE));
    IF FPOS <> INITPOS THEN GOTO 1;
    CLOSE (FROMF);
    NEWFP := $8000; {---atom file not on this image---}
    EXIT;
  END;
  FRZVERSION := NOT(ATMHEADER.STARTADRS AND ATMHEADER.EXECADRS);
  IF FRZVERSION > 3 THEN
  BEGIN {---normal file---}
    IF MEM[ATOMMEMSEG:TABLEOFS+$04] AND $80 <> $00 THEN
    BEGIN
      STARTADRS := MEMW[ATOMMEMSEG:TABLEOFS+$02];
    END ELSE
    BEGIN
      STARTADRS := ATMHEADER.STARTADRS;
    END;
    MEM[ATOMMEMSEG:$00DD] := $00;
    MEMW[ATOMMEMSEG:$00D6] := ATMHEADER.EXECADRS;
    {---no unnamed files, so no JMP ($00CB) will occur when *RUN---}
    DEST := PTR(ATOMMEMSEG,STARTADRS);
    SEEK (FROMF,FPOS);
    IF LONGINT(STARTADRS)+LONGINT(PRED(ATMHEADER.DATASIZE)) > $FFFF THEN
    BEGIN
      NR := 0;
    END ELSE
    BEGIN
      BLOCKREAD (FROMF,DEST^,ATMHEADER.DATASIZE,NR);
    END;
    IF NR <> ATMHEADER.DATASIZE THEN
    BEGIN
      CLOSE (FROMF);
      NEWFP := $8000; {---dos read error---}
      EXIT;
    END;
    {---ok, atom file loaded---}
    CLOSE (FROMF);
    INC (NEWFP);
  END ELSE
  BEGIN {---frozen file---}
    GETMEM (BUF,BUFSIZE);
    BUFSEG := SEG(BUF^);
    IF OFS(BUF^) <> $0000 THEN INC (BUFSEG);
    DEST := PTR(BUFSEG,$0000);
    SEEK (FROMF,FPOS);
    BLOCKREAD (FROMF,DEST^,ATMHEADER.DATASIZE,NR);
    IF NR <> ATMHEADER.DATASIZE THEN
    BEGIN
      CLOSE (FROMF);
      FREEMEM (BUF,BUFSIZE);
      NEWFP := $8000; {---dos read error---}
      EXIT;
    END;
    CLOSE (FROMF);
    ASM;
               MOV   BX,WORD PTR FRZVERSION
               PUSH  DS
               MOV   ES,WORD PTR ATOMMEMSEG
               SUB   DI,DI
               MOV   DS,WORD PTR BUFSEG
               SUB   SI,SI
               LODSW
               ADD   AX,SI
               MOV   DX,AX
    @UNPACK3:  CMP   SI,DX
               JZ    @UNPACK2
               MOVSB
               JMP   @UNPACK3
    @UNPACK2:  LODSW
               CMP   AX,$FFFF
               JZ    @UNPACK1
               ADD   AX,SI
               MOV   DX,AX
               LODSW
               MOV   CX,AX
               LODSB
               REPZ
               STOSB
               JMP   @UNPACK3
    @UNPACK1:  MOV   DI,$B000
               MOVSW
               MOVSW
               MOV   DI,$B800
               MOV   CX,$0008
               REPZ
               MOVSW
               PUSH  ES
               MOV   AX,$A000
               MOV   ES,AX
               CALL  CLRMOUSECURSOR
               POP   ES
               CMP   BX,$0001
               JB    @UNPACK4
               {freeze version 1, from emulator v1.30 and higher}
               PUSH  ES
               MOV   ES,WORD PTR [CS:DATASEG]
               LODSW
               MOV   WORD PTR TEMPMOUSEDAT[ES:$00],AX
               LODSB
               MOV   BYTE PTR TEMPMOUSEDAT[ES:$02],AL
               LODSW
               MOV   WORD PTR TEMPMOUSEDAT[ES:$03],AX
               LODSW
               MOV   WORD PTR TEMPMOUSEDAT[ES:$05],AX
               MOV   AX,$A000
               MOV   ES,AX
               CALL  ENABLEMOUSE
               POP   ES
               PUSH  ES
               MOV   AX,ES
               ADD   AX,$2000
               MOV   ES,AX
               SUB   DI,DI
               CMP   BX,$0002
               JAE   @UNPACK6
               {freeze version 1: up to 8 toolboxes}
               MOV   CX,$0080
               REPZ
               MOVSB
               MOV   CX,$0080
               MOV   AL,$00
               REPZ
               STOSB
               MOV   CX,$0040
               REPZ
               MOVSB
               JMP   @UNPACK7
    @UNPACK6:  {freeze version 2 and higher: up to 16 toolboxes}
               MOV   CX,$0140
               REPZ
               MOVSB
    @UNPACK7:  LODSB
               MOV   BYTE PTR [CS:AANTBOXRET],AL
               MOV   AX,CS
               MOV   ES,AX
               MOV   DI,OFFSET BOXRETURNS
               MOV   CX,$0020
               REPZ
               MOVSW
               POP   ES
               JMP   @UNPACK5
    @UNPACK4:  {freeze version 0, until emulator v1.30}
               MOV   DI,$BFE0
               SUB   AX,AX
               STOSW
               STOSB
               MOV   BYTE PTR [CS:MOUSENR],$80
    @UNPACK5:  MOV   DI,$BFF6
               MOVSW
               MOVSW
               MOVSW
               MOVSW
               MOVSW
               MOV   AX,CS
               MOV   ES,AX
               MOV   DI,OFFSET GRAPHMODE
               MOVSB
               MOV   DI,OFFSET PROGRAMCNT
               MOVSW
               MOV   DI,OFFSET STACKPOINTER
               MOVSW
               MOV   DI,OFFSET ACCUMULATOR
               MOVSB
               MOV   DI,OFFSET FLAGREGISTER
               MOVSB
               CMP   BX,$0003
               JB    @UNPACK8
               {freeze version 3 and higher: extra accumulator}
               MOV   DI,OFFSET XREGISTER
               MOVSB
               MOV   DI,OFFSET YREGISTER
               MOVSB
               MOV   DI,OFFSET ACCU_B
               MOVSB
               JMP   @UNPACK9
    @UNPACK8:  MOV   DI,OFFSET XREGISTER
               MOVSB
               INC   SI
               MOV   DI,OFFSET YREGISTER
               MOVSB
               INC   SI
    @UNPACK9:  MOV   DI,OFFSET CPUSPEEDMODE
               MOVSB
               MOV   DI,OFFSET ALTKEYB
               MOVSB
               MOV   DI,OFFSET T2L_L
               MOVSB
               MOV   DI,OFFSET IRQDELAY
               MOVSB
               POP   DS
               MOV   AX,CS
               MOV   ES,AX
               MOV   DI,OFFSET TOETS
               MOV   CX,$0082
               MOV   AL,$00
               REPZ
               STOSB
    END;
    FREEMEM (BUF,BUFSIZE);
    INC (NEWFP,$4001);
  END;
  ASM;
               MOV   ES,WORD PTR ATOMMEMSEG
               MOV   BYTE PTR [ES:FLIPFLOP],$55
               MOV   SI,OFFSET ATOMROMMEM + $1000
               MOV   DI,$C000
               MOV   CX,$2000
               REPZ
               MOVSW
               TEST  BYTE PTR [CS:LEENDERTSROM],$FF
               JZ    @SK2
               MOV   SI,OFFSET LEENDERTS_FPROM_DAT
               MOV   DI,$D000
               MOV   CX,LEENDERTS_FPROM_SIZE
               REPZ
               MOVSB
  @SK2:        TEST  BYTE PTR [CS:IGNOREzpFEh],$FF
               JZ    @SK1
               MOV   BYTE PTR [ES:$FF07],$00
  @SK1:        PUSH  DS
               MOV   DS,WORD PTR ATOMMEMSEG
               PUSH  WORD PTR [$0090]
               PUSH  WORD PTR [$0092]
               PUSH  WORD PTR [$0094]
               PUSH  WORD PTR [$0096]
               PUSH  WORD PTR [$0098]
               CALL  SETA000MEM
               POP   WORD PTR [$0098]
               POP   WORD PTR [$0096]
               POP   WORD PTR [$0094]
               POP   WORD PTR [$0092]
               POP   WORD PTR [$0090]
               POP   DS
  END;
END;

{---[readfinbuf]------------------------------------------------------------}
PROCEDURE READFINBUF (NAMEOFFSET:WORD; FILEPOINTER:INTEGER; VAR NEWFP: WORD);
LABEL 1;
VAR FROMF     : FILE;
    TAPESIZE  : LONGINT;
    FILENAME  : STRING[16];
    CURNAME   : STRING[16];
    ATMHEADER : ATMFILEREC;
    FPOS      : LONGINT;
    INITPOS   : LONGINT;
    I         : WORD;
    NR        : WORD;
    DUMMY     : INTEGER;
BEGIN
  FINBUFPTR := $0000;
  FINSIZE := 0;
  IF LENGTH(TAPEIMAGENAME) = 0 THEN
  BEGIN
    NEWFP := $8000; {---no tape image selected---}
    EXIT;
  END;
  FILENAME := '';
  I := 0;
  WHILE (I < 16) AND (MEM[ATOMMEMSEG:NAMEOFFSET+I] <> $0D) DO
  BEGIN
    FILENAME := FILENAME + CHR(MEM[ATOMMEMSEG:NAMEOFFSET+I]);
    INC(I);
  END;
  IF LENGTH(FILENAME) = 0 THEN FILENAME := '*';
  DUMMY := IORESULT;
  ASSIGN (FROMF,TAPEIMAGENAME+'.TAP');
  RESET (FROMF,1);
  IF IORESULT <> 0 THEN
  BEGIN
    NEWFP := $8000; {---tape image not found---}
    EXIT;
  END;
  TAPESIZE := FILESIZE(FROMF);
  NEWFP := 0;
  FPOS := 0;
  WHILE (FPOS < TAPESIZE) AND (FILEPOINTER > 0) DO
  BEGIN
    ATMHEADER := ATOMFILES[NEWFP];
    INC (FPOS,SIZEOF(ATMHEADER)+LONGINT(ATMHEADER.DATASIZE));
    DEC (FILEPOINTER);
    INC (NEWFP);
  END;
  INITPOS := FPOS;
  IF INITPOS = 0 THEN INITPOS := TAPESIZE;
1:IF FPOS >= TAPESIZE THEN
  BEGIN
    NEWFP := 0;
    FPOS := 0;
  END;
  ATMHEADER := ATOMFILES[NEWFP];
  INC (FPOS,SIZEOF(ATMHEADER));
  CURNAME := '';
  I := 0;
  WHILE (I < 16) AND (ATMHEADER.ATMNAME[I] <> #$00) DO
  BEGIN
    CURNAME := CURNAME + ATMHEADER.ATMNAME[I];
    INC (I);
  END;
  IF (FILENAME[LENGTH(FILENAME)] = '*') THEN
  BEGIN
    IF (LENGTH(FILENAME) = 1) OR
       (COPY(FILENAME,1,PRED(LENGTH(FILENAME))) =
        COPY (CURNAME,1,PRED(LENGTH(FILENAME)))) THEN FILENAME := CURNAME;
  END;
  IF FILENAME <> CURNAME THEN
  BEGIN
    INC (NEWFP);
    INC (FPOS,LONGINT(ATMHEADER.DATASIZE));
    IF FPOS <> INITPOS THEN GOTO 1;
    CLOSE (FROMF);
    NEWFP := $8000; {---file not on this image---}
    EXIT;
  END;
  SEEK (FROMF,FPOS);
  BLOCKREAD (FROMF,FINBUF^,ATMHEADER.DATASIZE,NR);
  IF NR <> ATMHEADER.DATASIZE THEN
  BEGIN
    CLOSE (FROMF);
    NEWFP := $8000; {---dos read error---}
    EXIT;
  END;
  {---ok, file loaded into finbuf---}
  CLOSE (FROMF);
  FINSIZE := ATMHEADER.DATASIZE;
  INC (NEWFP);
END;

{---[createfout]------------------------------------------------------------}
PROCEDURE CREATEFOUT;
VAR TOF       : FILE;
    ATMHEADER : ATMFILEREC;
    I         : BYTE;
    NW        : WORD;
    DUMMY     : INTEGER;
BEGIN
  IF LENGTH(TAPEIMAGENAME) = 0 THEN EXIT;
  DUMMY := IORESULT;
  ASSIGN (TOF,TAPEIMAGENAME+'.TAP');
  RESET (TOF,1);
  IF IORESULT <> 0 THEN EXIT;
  SEEK (TOF,FILESIZE(TOF));
  FOR I := 0 TO 15 DO ATMHEADER.ATMNAME[I] := #$00;
  FOR I := 1 TO LENGTH(FOUTNAME) DO ATMHEADER.ATMNAME[PRED(I)] := FOUTNAME[I];
  ATMHEADER.STARTADRS := $8200;
  ATMHEADER.EXECADRS := $C2B2;
  ATMHEADER.DATASIZE := 0;
  BLOCKWRITE (TOF,ATMHEADER,SIZEOF(ATMHEADER),NW);
  CLOSE (TOF);
  READFILESINTAPEIMAGE;
END;

{---[writefoutbuf]----------------------------------------------------------}
PROCEDURE WRITEFOUTBUF;
VAR TOF       : FILE;
    TAPESIZE  : LONGINT;
    CURNAME   : STRING[16];
    ATMHEADER : ATMFILEREC;
    FPOS      : LONGINT;
    PREV      : LONGINT;
    I         : WORD;
    NW        : WORD;
    DUMMY     : INTEGER;
BEGIN
  IF (FOUTOPEN=0) OR (FOUTBUFPTR=0) THEN EXIT;
  IF LENGTH(TAPEIMAGENAME) = 0 THEN
  BEGIN
    FOUTERRORSND;
    FOUTOPEN := 0;
    EXIT;
  END;
  DUMMY := IORESULT;
  ASSIGN (TOF,TAPEIMAGENAME+'.TAP');
  RESET (TOF,1);
  IF IORESULT <> 0 THEN
  BEGIN
    FOUTERRORSND;
    FOUTOPEN := 0;
    EXIT;
  END;
  TAPESIZE := FILESIZE(TOF);
  FPOS := 0;
  PREV := 0;
  I := 0;
  WHILE FPOS < TAPESIZE DO
  BEGIN
    PREV := FPOS;
    ATMHEADER := ATOMFILES[I];
    INC (FPOS,SIZEOF(ATMHEADER)+LONGINT(ATMHEADER.DATASIZE));
    INC (I);
  END;
  FPOS := PREV;
  CURNAME := '';
  I := 0;
  WHILE (I < 16) AND (ATMHEADER.ATMNAME[I] <> #$00) DO
  BEGIN
    CURNAME := CURNAME + ATMHEADER.ATMNAME[I];
    INC (I);
  END;
  IF (CURNAME <> FOUTNAME) OR (TAPEIMAGENAME <> IMAGEFOUTNAME) THEN
  BEGIN
    CLOSE (TOF);
    FOUTERRORSND;
    FOUTOPEN := 0;
    EXIT;
  END;
  INC (ATMHEADER.DATASIZE,FOUTBUFPTR);
  SEEK (TOF,FPOS);
  BLOCKWRITE (TOF,ATMHEADER,SIZEOF(ATMHEADER),NW);
  SEEK (TOF,TAPESIZE);
  BLOCKWRITE (TOF,FOUTBUF^,FOUTBUFPTR,NW);
  CLOSE (TOF);
  FOUTBUFPTR := 0;
  READFILESINTAPEIMAGE;
END;

{---[writebmp]--------------------------------------------------------------}
PROCEDURE WRITEBMP;
LABEL 1,2;
CONST BUFSIZE = $6000;
VAR TOF    : FILE;
    BMPNR  : ARRAY[1..4] OF CHAR;
    I      : BYTE;
    BUF    : POINTER;
    BUFOFS : WORD;
    BUFSEG : WORD;
    NR     : WORD;
BEGIN
  FOR I := 0 TO SIZEOF(BMPHEADER) DO BMPHEADER[I] := $00;
  BMPHEADER[$00] := $42; BMPHEADER[$01] := $4D; BMPHEADER[$02] := $76;
  BMPHEADER[$03] := $70; BMPHEADER[$0A] := $76; BMPHEADER[$0E] := $28;
  BMPHEADER[$13] := $01; BMPHEADER[$16] := $C0; BMPHEADER[$1A] := $01;
  BMPHEADER[$1C] := $04; BMPHEADER[$23] := $60; BMPHEADER[$2E] := $10;
  BMPHEADER[$32] := $10;
  ASM;
               MOV   CX,$0010
               SUB   SI,SI
               SUB   DI,DI
  @LP1:        MOV   AL,BYTE PTR EMULCOLORS[CS:SI]
               SHL   AL,2
               MOV   BYTE PTR BMPHEADER[DI+$0038],AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:SI+$01]
               SHL   AL,2
               MOV   BYTE PTR BMPHEADER[DI+$0037],AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:SI+$02]
               SHL   AL,2
               MOV   BYTE PTR BMPHEADER[DI+$0036],AL
               ADD   SI,+$03
               ADD   DI,+$04
               LOOP  @LP1
  END;
  GETMEM (BUF,BUFSIZE);
  BUFOFS := OFS(BUF^);
  BUFSEG := SEG(BUF^);
  ASM;
               PUSH  DS
               MOV   DI,WORD PTR BUFOFS
               MOV   ES,WORD PTR BUFSEG
               MOV   SI,$0140+191*$0120
               MOV   AX,$A000
               MOV   DS,AX
               MOV   DL,+192
  @LP1:        MOV   DH,$40
  @LP2:        MOV   BX,$C0C0
               SUB   CX,CX
  @LP3:        MOV   AX,WORD PTR [SI]
               AND   AX,BX
               TEST  AH,$FF
               JZ    @SK1
               OR    CL,$02
  @SK1:        TEST  AL,$FF
               JZ    @SK2
               OR    CL,$01
  @SK2:        MOV   AX,WORD PTR [SI+$02]
               AND   AX,BX
               TEST  AH,$FF
               JZ    @SK3
               OR    CL,$08
  @SK3:        TEST  AL,$FF
               JZ    @SK4
               OR    CL,$04
  @SK4:        ROL   CX,4
               SHR   BX,2
               JNZ   @LP3
               ROR   CX,4
               XCHG  CL,CH
               MOV   WORD PTR [ES:DI],CX
               ADD   SI,+$04
               ADD   DI,+$02
               DEC   DH
               JNZ   @LP2
               SUB   SI,$40*4+$0120
               DEC   DL
               JNZ   @LP1
               POP   DS
  END;
  BMPNR := '0000';
1:ASSIGN (TOF,'ATOM'+BMPNR+'.BMP');
  RESET (TOF,1);
  IF IORESULT = 0 THEN
  BEGIN
    CLOSE (TOF);
    I := 4;
2:  INC (BMPNR[I]);
    IF BMPNR[I] > '9' THEN
    BEGIN
      BMPNR[I] := '0';
      DEC (I);
      IF I >= 1 THEN GOTO 2;
      FREEMEM (BUF,BUFSIZE);
      EXIT;
    END;
    GOTO 1;
  END;
  REWRITE (TOF,1);
  BLOCKWRITE (TOF,BMPHEADER,SIZEOF(BMPHEADER),NR);
  BLOCKWRITE (TOF,BUF^,BUFSIZE,NR);
  CLOSE (TOF);
  FREEMEM (BUF,BUFSIZE);
END;

{---[insertinimage]---------------------------------------------------------}
PROCEDURE INSERTINIMAGE (FILEPTR:INTEGER; HEADER:ATMFILEREC; DATA:POINTER;
                         VAR CODE:WORD);
CONST BUFSIZE = $1000;
VAR FROMF,TOF : FILE;
    I         : WORD;
    NR,NW     : WORD;
    FPOS      : LONGINT;
    AANT      : LONGINT;
    MAX       : WORD;
    BUF       : POINTER;
    TMPHEADER : ATMFILEREC;
    DUMMY     : INTEGER;
BEGIN
  IF LENGTH(TAPEIMAGENAME) = 0 THEN
  BEGIN
    CODE := $8000; {---no tape image selected---}
    EXIT;
  END;
  DUMMY := IORESULT;
  ASSIGN (FROMF,TAPEIMAGENAME+'.TAP');
  RESET (FROMF,1);
  IF IORESULT <> 0 THEN
  BEGIN
    CODE := $8000; {---tape image not found---}
    EXIT;
  END;
  ASSIGN (TOF,'ATOMTEMP.TMP');
  REWRITE (TOF,1);
  IF IORESULT <> 0 THEN
  BEGIN
    CLOSE (FROMF);
    CODE := $8000; {---dos write error---}
    EXIT;
  END;
  FPOS := 0;
  I := 0;
  WHILE I < FILEPTR DO
  BEGIN
    TMPHEADER := ATOMFILES[I];
    INC (FPOS,SIZEOF(TMPHEADER)+LONGINT(TMPHEADER.DATASIZE));
    INC (I);
  END;
  AANT := FPOS;
  GETMEM (BUF,BUFSIZE);
  WHILE AANT > 0 DO
  BEGIN
    MAX := BUFSIZE;
    IF MAX > AANT THEN MAX := AANT;
    BLOCKREAD (FROMF,BUF^,MAX,NR);
    BLOCKWRITE (TOF,BUF^,NR,NW);
    IF NR<>NW THEN
    BEGIN
      FREEMEM (BUF,BUFSIZE);
      CLOSE (TOF);
      ERASE (TOF);
      CLOSE (FROMF);
      CODE := $8000; {---dos read/write error---}
      EXIT;
    END;
    DEC (AANT,LONGINT(NW));
  END;
  BLOCKWRITE (TOF,HEADER,SIZEOF(HEADER),NW);
  IF NW <> SIZEOF(HEADER) THEN
  BEGIN
    FREEMEM (BUF,BUFSIZE);
    CLOSE (TOF);
    ERASE (TOF);
    CLOSE (FROMF);
    CODE := $8000; {---dos write error---}
    EXIT;
  END;
  BLOCKWRITE (TOF,DATA^,HEADER.DATASIZE,NW);
  IF NW <> HEADER.DATASIZE THEN
  BEGIN
    FREEMEM (BUF,BUFSIZE);
    CLOSE (TOF);
    ERASE (TOF);
    CLOSE (FROMF);
    CODE := $8000; {---dos write error---}
    EXIT;
  END;
  IF FILEPTR < AANTALATOMFILES THEN
  BEGIN
    REPEAT
      BLOCKREAD (FROMF,BUF^,BUFSIZE,NR);
      BLOCKWRITE (TOF,BUF^,NR,NW);
    UNTIL NR=0;
  END;
  FREEMEM (BUF,BUFSIZE);
  CLOSE (TOF);
  CLOSE (FROMF);
  ERASE (FROMF);
  RENAME (TOF,TAPEIMAGENAME+'.TAP');
  READFILESINTAPEIMAGE;
  CODE := $0000;
END;

{---[save]------------------------------------------------------------------}
PROCEDURE SAVE (TABLEOFS:WORD; FILEPOINTER:INTEGER; VAR CODE:WORD);
VAR W         : WORD;
    I         : WORD;
    FILENAME  : STRING[16];
    ATMHEADER : ATMFILEREC;
    SOURCE    : POINTER;
BEGIN
  W := MEMW[ATOMMEMSEG:TABLEOFS];
  FILENAME := '';
  I := 0;
  WHILE (I < 16) AND (MEM[ATOMMEMSEG:W+I] <> $0D) DO
  BEGIN
    FILENAME := FILENAME + CHR(MEM[ATOMMEMSEG:W+I]);
    INC(I);
  END;
  IF LENGTH(FILENAME)=0 THEN FILENAME := 'FILE';
  FOR I := 0 TO 15 DO ATMHEADER.ATMNAME[I] := #$00;
  FOR I := 1 TO LENGTH(FILENAME) DO ATMHEADER.ATMNAME[PRED(I)] := FILENAME[I];
  ATMHEADER.STARTADRS := MEMW[ATOMMEMSEG:TABLEOFS+2];
  ATMHEADER.EXECADRS := MEMW[ATOMMEMSEG:TABLEOFS+4];
  W := MEMW[ATOMMEMSEG:TABLEOFS+8] - MEMW[ATOMMEMSEG:TABLEOFS+6];
  ATMHEADER.DATASIZE := W;
  SOURCE := PTR(ATOMMEMSEG,MEMW[ATOMMEMSEG:TABLEOFS+6]);
  INSERTINIMAGE (FILEPOINTER,ATMHEADER,SOURCE,CODE);
END;

{---[freeze]----------------------------------------------------------------}
PROCEDURE FREEZE;
CONST BUFSIZE = $FFF8;
VAR TOF       : FILE;
    BUF       : POINTER;
    P         : POINTER;
    BUFSEG    : WORD;
    LASTOFS   : WORD;
    SRC       : WORD;
    DST       : WORD;
    AANT      : WORD;
    NR        : WORD;
    B         : BYTE;
    ATMHEADER : ATMFILEREC;
    DUMMY     : INTEGER;
BEGIN
  IF AANTALATOMFILES >= MAXAANTFILES THEN EXIT;
  ATMHEADER.ATMNAME := 'FROZEN FILE'+#0+#0+#0+#0+#0;
  GETMEM (BUF,BUFSIZE);
  BUFSEG := SEG(BUF^);
  IF OFS(BUF^) <> $0000 THEN INC (BUFSEG);
  LASTOFS := $0000;
  DST := $0002;
  SRC := $0000;
  WHILE SRC <= $9FFF DO
  BEGIN
    B := MEM[ATOMMEMSEG:SRC];
    IF SRC <= $9FFB THEN
    BEGIN
      IF (B = MEM[ATOMMEMSEG:SRC+1]) AND
         (B = MEM[ATOMMEMSEG:SRC+2]) AND
         (B = MEM[ATOMMEMSEG:SRC+3]) AND
         (B = MEM[ATOMMEMSEG:SRC+4]) THEN
      BEGIN
        AANT := 5;
        WHILE (SRC+AANT <= $9FFF) AND (B = MEM[ATOMMEMSEG:SRC+AANT]) DO INC (AANT);
        MEMW[BUFSEG:LASTOFS] := DST-(LASTOFS+2);
        LASTOFS := DST;
        INC (DST,2);
        MEMW[BUFSEG:DST] := AANT;
        INC (DST,2);
        MEM[BUFSEG:DST] := B;
        INC (DST);
        INC (SRC,AANT);
      END ELSE
      BEGIN
        MEM[BUFSEG:DST] := B;
        INC (DST);
        INC (SRC);
      END;
    END ELSE
    BEGIN
      MEM[BUFSEG:DST] := B;
      INC (DST);
      INC (SRC);
    END;
  END;
  MEMW[BUFSEG:LASTOFS] := DST-(LASTOFS+2);
  MEMW[BUFSEG:DST] := $FFFF;
  INC (DST,2);
  FOR SRC := $B000 TO $B003 DO
  BEGIN
    MEM[BUFSEG:DST] := MEM[ATOMMEMSEG:SRC];
    INC (DST);
  END;
  FOR SRC := $B800 TO $B80F DO
  BEGIN
    MEM[BUFSEG:DST] := MEM[ATOMMEMSEG:SRC];
    INC (DST);
  END;
  MEM[BUFSEG:DST] := TEMPMOUSEDAT.B_BFE0;
  INC (DST);
  MEM[BUFSEG:DST] := TEMPMOUSEDAT.B_BFE1;
  INC (DST);
  MEM[BUFSEG:DST] := TEMPMOUSEDAT.B_MOUSENR;
  INC (DST);
  MEMW[BUFSEG:DST] := TEMPMOUSEDAT.MOUSEX;
  INC (DST,2);
  MEMW[BUFSEG:DST] := TEMPMOUSEDAT.MOUSEY;
  INC (DST,2);
  FOR SRC := $0000 TO $013F DO
  BEGIN
    MEM[BUFSEG:DST] := MEM[ATOMMEMSEG+$2000:SRC];
    INC (DST);
  END;
  MEM[BUFSEG:DST] := MEM[CSEG:OFS(AANTBOXRET)];
  INC (DST);
  FOR SRC := $00 TO $3F DO
  BEGIN
    MEM[BUFSEG:DST] := MEM[CSEG:OFS(BOXRETURNS)+SRC];
    INC (DST);
  END;
  FOR SRC := $BFF6 TO $BFFF DO
  BEGIN
    MEM[BUFSEG:DST] := MEM[ATOMMEMSEG:SRC];
    INC (DST);
  END;
  MEM [BUFSEG:DST] := MEM [CSEG:OFS(GRAPHMODE)];    INC (DST);
  MEMW[BUFSEG:DST] := MEMW[CSEG:OFS(PROGRAMCNT)];   INC (DST,2);
  MEMW[BUFSEG:DST] := MEMW[CSEG:OFS(STACKPOINTER)]; INC (DST,2);
  MEM [BUFSEG:DST] := MEM [CSEG:OFS(ACCUMULATOR)];  INC (DST);
  MEM [BUFSEG:DST] := MEM [CSEG:OFS(FLAGREGISTER)]; INC (DST);
  MEM [BUFSEG:DST] := MEM [CSEG:OFS(XREGISTER)];    INC (DST);
  MEM [BUFSEG:DST] := MEM [CSEG:OFS(YREGISTER)];    INC (DST);
  MEM [BUFSEG:DST] := MEM [CSEG:OFS(ACCU_B)];       INC (DST);
  MEM [BUFSEG:DST] := MEM [CSEG:OFS(CPUSPEEDMODE)]; INC (DST);
  MEM [BUFSEG:DST] := MEM [CSEG:OFS(ALTKEYB)];      INC (DST);
  MEM [BUFSEG:DST] := MEM [CSEG:OFS(T2L_L)];        INC (DST);
  MEM [BUFSEG:DST] := MEM [CSEG:OFS(IRQDELAY)];     INC (DST);
  P := PTR (BUFSEG,$0000);
  DUMMY := IORESULT;
  ASSIGN (TOF,TAPEIMAGENAME+'.TAP');
  RESET (TOF,1);
  IF IORESULT <> 0 THEN
  BEGIN
    FREEMEM (BUF,BUFSIZE);
    EXIT;
  END;
  SEEK (TOF,FILESIZE(TOF));
  ATMHEADER.STARTADRS := $FFFF;
  ATMHEADER.EXECADRS := $FFFC; {not (freeze version)}
  ATMHEADER.DATASIZE := DST;
  BLOCKWRITE (TOF,ATMHEADER,SIZEOF(ATMHEADER),NR);
  BLOCKWRITE (TOF,P^,DST,NR);
  CLOSE (TOF);
  ATOMFILES[AANTALATOMFILES] := ATMHEADER;
  INC (AANTALATOMFILES);
  FREEMEM (BUF,BUFSIZE);
END;

{---[deletefile]------------------------------------------------------------}
PROCEDURE DELETEFILE (WHICHFILE:WORD);
CONST BUFSIZE = $8000;
VAR FROMF,TOF : FILE;
    ATMHEADER : ATMFILEREC;
    FPOS      : LONGINT;
    AANT      : LONGINT;
    I,MAX     : WORD;
    NR,NW     : WORD;
    BUF       : POINTER;
    DUMMY     : INTEGER;
BEGIN
  DUMMY := IORESULT;
  ASSIGN (FROMF,TAPEIMAGENAME+'.TAP');
  RESET (FROMF,1);
  IF IORESULT <> 0 THEN EXIT;
  ASSIGN (TOF,'ATOMTEMP.TMP');
  REWRITE (TOF,1);
  IF IORESULT <> 0 THEN
  BEGIN
    CLOSE (FROMF);
    EXIT;
  END;
  FPOS := 0;
  I := 0;
  WHILE I < WHICHFILE DO
  BEGIN
    ATMHEADER := ATOMFILES[I];
    INC (FPOS,SIZEOF(ATMHEADER)+LONGINT(ATMHEADER.DATASIZE));
    INC (I);
  END;
  AANT := FPOS;
  GETMEM (BUF,BUFSIZE);
  WHILE AANT > 0 DO
  BEGIN
    MAX := BUFSIZE;
    IF MAX > AANT THEN MAX := AANT;
    BLOCKREAD (FROMF,BUF^,MAX,NR);
    BLOCKWRITE (TOF,BUF^,NR,NW);
    IF NR<>NW THEN
    BEGIN
      FREEMEM (BUF,BUFSIZE);
      CLOSE (TOF);
      ERASE (TOF);
      CLOSE (FROMF);
      EXIT;
    END;
    DEC (AANT,LONGINT(NW));
  END;
  ATMHEADER := ATOMFILES[I];
  INC (FPOS,SIZEOF(ATMHEADER)+LONGINT(ATMHEADER.DATASIZE));
  SEEK (FROMF,FPOS);
  IF WHICHFILE < AANTALATOMFILES THEN
  BEGIN
    REPEAT
      BLOCKREAD (FROMF,BUF^,BUFSIZE,NR);
      BLOCKWRITE (TOF,BUF^,NR,NW);
    UNTIL (NR=0);
  END;
  FREEMEM (BUF,BUFSIZE);
  CLOSE (TOF);
  CLOSE (FROMF);
  ERASE (FROMF);
  RENAME (TOF,TAPEIMAGENAME+'.TAP');
  READFILESINTAPEIMAGE;
END;

{---[export]----------------------------------------------------------------}
PROCEDURE EXPORT (WHICHFILE:WORD);
CONST BUFSIZE = $8000;
VAR FROMF,TOF : FILE;
    ATMHEADER : ATMFILEREC;
    FILENAME  : STRING[16];
    CH        : CHAR;
    I,AANT    : WORD;
    NR,NW     : WORD;
    FPOS      : LONGINT;
    BUF       : POINTER;
    DUMMY     : INTEGER;
BEGIN
  ATMHEADER := ATOMFILES[WHICHFILE];
  FILENAME := '';
  I := 0;
  WHILE (I < 16) AND (ATMHEADER.ATMNAME[I] <> #$0D) DO
  BEGIN
    CH := ATMHEADER.ATMNAME[I];
    IF ((CH >= '0') AND (CH <= '9')) OR ((CH >= 'A') AND (CH <= 'Z')) THEN
    BEGIN
      FILENAME := FILENAME + CH;
    END;
    INC(I);
  END;
  IF LENGTH(FILENAME) = 0 THEN FILENAME := 'FILE';
  IF LENGTH(FILENAME) > 8 THEN
  BEGIN
    I := LENGTH(FILENAME);
    WHILE (LENGTH(FILENAME) > 8) AND (I > 0) DO
    BEGIN
      IF ((FILENAME[I] <= 'A') OR (FILENAME[I] = 'E') OR
          (FILENAME[I] = 'I') OR (FILENAME[I] = 'O') OR
          (FILENAME[I] = 'U') OR (FILENAME[I] = 'Y') OR
          (FILENAME[I] > 'Z'))
         AND NOT ((FILENAME[I] >= '0') AND (FILENAME[I] <= '9')) THEN
      BEGIN
        DELETE (FILENAME,I,1);
        I := LENGTH(FILENAME);
      END ELSE
      BEGIN
        DEC (I);
      END;
    END;
    IF LENGTH(FILENAME) > 8 THEN FILENAME := COPY(FILENAME,1,8);
  END;
  DUMMY := IORESULT;
  ASSIGN (TOF,FILENAME+'.ATM');
  RESET (TOF,1);
  IF IORESULT = 0 THEN
  BEGIN
    CLOSE (TOF);
    ERRORSND;
    EXIT;
  END;
  REWRITE (TOF,1);
  IF IORESULT <> 0 THEN EXIT;
  BLOCKWRITE (TOF,ATMHEADER,SIZEOF(ATMHEADER),NW);
  IF NW <> SIZEOF(ATMHEADER) THEN
  BEGIN
    CLOSE (TOF);
    ERASE (TOF);
    EXIT;
  END;
  ASSIGN (FROMF,TAPEIMAGENAME+'.TAP');
  RESET (FROMF,1);
  IF IORESULT <> 0 THEN
  BEGIN
    CLOSE (TOF);
    ERASE (TOF);
    EXIT;
  END;
  FPOS := 0;
  I := 0;
  WHILE I < WHICHFILE DO
  BEGIN
    ATMHEADER := ATOMFILES[I];
    INC (FPOS,SIZEOF(ATMHEADER)+LONGINT(ATMHEADER.DATASIZE));
    INC (I);
  END;
  INC (FPOS,SIZEOF(ATMHEADER));
  SEEK (FROMF,FPOS);
  IF IORESULT <> 0 THEN
  BEGIN
    CLOSE (FROMF);
    CLOSE (TOF);
    ERASE (TOF);
    EXIT;
  END;
  I := ATOMFILES[WHICHFILE].DATASIZE;
  GETMEM (BUF,BUFSIZE);
  REPEAT
    AANT := I;
    IF AANT > BUFSIZE THEN AANT := BUFSIZE;
    DEC (I,AANT);
    BLOCKREAD (FROMF,BUF^,AANT,NR);
    BLOCKWRITE (TOF,BUF^,NR,NW);
  UNTIL I=0;
  FREEMEM (BUF,BUFSIZE);
  CLOSE (FROMF);
  CLOSE (TOF);
END;

{---[import]----------------------------------------------------------------}
PROCEDURE IMPORT (ATMFILEPTR,IMPFILEPTR:INTEGER; VAR CODE:WORD);
CONST BUFSIZE = $FFF8;
VAR BUF       : POINTER;
    BUFOFS    : WORD;
    BUFSEG    : WORD;
    ATMHEADER : ATMFILEREC;
    FILENAME  : STRING[13];
    FILEHANDLE: WORD;
    FNOFS     : WORD;
    ATOFS     : WORD;
    NR        : WORD;
    RESULTAAT : BYTE;
CONST ATMSIZE = SIZEOF(ATMHEADER);
BEGIN
  CODE := $8000;
  FILENAME := '';
  NR := 0;
  WHILE (NR < 12) AND (IMPFILES[IMPFILEPTR].ATMNAME[NR] <> #$00) DO
  BEGIN
    FILENAME := FILENAME + IMPFILES[IMPFILEPTR].ATMNAME[NR];
    INC (NR);
  END;
  FILENAME := FILENAME + #$00;
  FNOFS := SUCC(OFS(FILENAME));
  ATOFS := OFS(ATMHEADER);
  GETMEM (BUF,BUFSIZE);
  BUFOFS := OFS(BUF^);
  BUFSEG := SEG(BUF^);
  ASM;
               MOV   BYTE PTR RESULTAAT,$01
               PUSH  DS
               MOV   AX,$3D00
               MOV   DX,WORD PTR FNOFS
               PUSH  SS
               POP   DS
               INT   $21 {open file}
               POP   DS
               JC    @EINDE
               MOV   WORD PTR FILEHANDLE,AX
               PUSH  DS
               MOV   AH,$3F {read from file}
               MOV   BX,WORD PTR FILEHANDLE
               MOV   CX,ATMSIZE
               MOV   DX,WORD PTR ATOFS
               PUSH  SS
               POP   DS
               INT   $21
               POP   DS
               JC    @CLOSE
               CMP   AX,ATMSIZE
               JNZ   @CLOSE
               PUSH  DS
               MOV   AH,$3F {read from file}
               MOV   BX,WORD PTR FILEHANDLE
               MOV   CX,WORD PTR ATMHEADER[$0014] {atmheader.datasize}
               MOV   DX,WORD PTR BUFOFS
               MOV   DS,WORD PTR BUFSEG
               INT   $21
               POP   DS
               JC    @CLOSE
               CMP   AX,WORD PTR ATMHEADER[$0014]
               JNZ   @CLOSE
               MOV   BYTE PTR RESULTAAT,$00
  @CLOSE:      MOV   AH,$3E {close file}
               MOV   BX,WORD PTR FILEHANDLE
               INT   $21
  @EINDE:
  END;
  IF RESULTAAT = 0 THEN INSERTINIMAGE (ATMFILEPTR,ATMHEADER,BUF,CODE)
                   ELSE ERRORSND;
  FREEMEM (BUF,BUFSIZE);
END;

{---[renamefile]------------------------------------------------------------}
PROCEDURE RENAMEFILE (WHICHFILE:INTEGER; SEGM,ADRS:WORD);
VAR F       : FILE;
    I       : WORD;
    NW      : WORD;
    FPOS    : LONGINT;
    SOURCE  : POINTER;
    DUMMY   : INTEGER;
BEGIN
  DUMMY := IORESULT;
  ASSIGN (F,TAPEIMAGENAME+'.TAP');
  RESET (F,1);
  IF IORESULT <> 0 THEN
  BEGIN
    CLOSE (F);
    EXIT;
  END;
  FPOS := 0;
  I := 0;
  WHILE I < WHICHFILE DO
  BEGIN
    INC (FPOS,SIZEOF(ATMFILEREC)+LONGINT(ATOMFILES[I].DATASIZE));
    INC (I);
  END;
  SEEK (F,FPOS);
  IF IORESULT <> 0 THEN
  BEGIN
    CLOSE (F);
    EXIT;
  END;
  SOURCE := PTR(SEGM,ADRS);
  MOVE (SOURCE^,ATOMFILES[WHICHFILE].ATMNAME,$10);
  BLOCKWRITE (F,ATOMFILES[WHICHFILE],SIZEOF(ATMFILEREC),NW);
  CLOSE (F);
  IF NW <> SIZEOF(ATMFILEREC) THEN READFILESINTAPEIMAGE;
END;

{---[createtapefile]--------------------------------------------------------}
PROCEDURE CREATETAPEFILE (SEGM,ADRS:WORD; VAR NEWTAPEPTR:WORD);
VAR F        : FILE;
    FILENAME : STRING[8];
    I        : WORD;
    DUMMY    : INTEGER;
BEGIN
  FILENAME := '';
  I := 0;
  WHILE (I < 8) AND (MEM[SEGM:ADRS+I] <> $00) DO
  BEGIN
    FILENAME := FILENAME + CHR(MEM[SEGM:ADRS+I]);
    INC (I);
  END;
  IF LENGTH(FILENAME) = 0 THEN FILENAME := 'NEWTAPE';
  DUMMY := IORESULT;
  ASSIGN (F,FILENAME+'.TAP');
  RESET (F,1);
  IF IORESULT = 0 THEN
  BEGIN
    CLOSE (F);
    ERRORSND;
    EXIT;
  END;
  REWRITE (F,1);
  CLOSE (F);
  READDIRECTORY;
  COPYWRITEPROT;
  NEWTAPEPTR := 0;
  WHILE FILENAME <> TAPEIMAGES[NEWTAPEPTR] DO INC(NEWTAPEPTR);
  TAPEIMAGENAME := FILENAME;
  READFILESINTAPEIMAGE;
END;

{---[creatediskfile]--------------------------------------------------------}
PROCEDURE CREATEDISKFILE (SEGM,ADRS:WORD; VAR NEWDISKPTR:WORD);
TYPE BUFTYPE = ARRAY[$00..$FF] OF BYTE;
VAR F        : FILE;
    FILENAME : STRING[8];
    I        : WORD;
    DUMMY    : INTEGER;
    BUF      : ^BUFTYPE;
BEGIN
  FILENAME := '';
  I := 0;
  WHILE (I < 8) AND (MEM[SEGM:ADRS+I] <> $00) DO
  BEGIN
    FILENAME := FILENAME + CHR(MEM[SEGM:ADRS+I]);
    INC (I);
  END;
  IF LENGTH(FILENAME) = 0 THEN FILENAME := 'NEWDISK';
  DUMMY := IORESULT;
  ASSIGN (F,FILENAME+'.DSK');
  RESET (F,1);
  IF IORESULT = 0 THEN
  BEGIN
    CLOSE (F);
    ERRORSND;
    EXIT;
  END;
  REWRITE (F,1);
  GETMEM (BUF,SIZEOF(BUFTYPE));
  FOR I := $00 TO $07 DO BUF^[I] := $20;
  FOR I := $08 TO PRED(SIZEOF(BUFTYPE)) DO BUF^[I] := $00;
  BLOCKWRITE (F,BUF^,SIZEOF(BUFTYPE));
  BUF^[$05] := $00;
  BUF^[$06] := $01;
  BUF^[$07] := $90;
  BLOCKWRITE (F,BUF^,SIZEOF(BUFTYPE));
  FOR I := $00 TO PRED(SIZEOF(BUFTYPE)) DO BUF^[I] := $E5;
  FOR I := 2 TO PRED(40*10) DO BLOCKWRITE (F,BUF^,SIZEOF(BUFTYPE));
  FREEMEM (BUF,SIZEOF(BUFTYPE));
  CLOSE (F);
  READDIRECTORY;
  COPYWRITEPROT;
  NEWDISKPTR := 0;
  WHILE FILENAME <> DISKIMAGES[NEWDISKPTR] DO INC(NEWDISKPTR);
  READFILESINTAPEIMAGE;
END;

{---[tijd]------------------------------------------------------------------}
FUNCTION TIJD:LONGINT;
VAR H,M,S,T:WORD;
BEGIN
  GETTIME (H,M,S,T);
  TIJD := LONGINT(T) + LONGINT(S)*100 + LONGINT(M)*100*60 +
          LONGINT(H)*100*60*60;
END;

{---[wachteventjes (english: wait a moment)]--------------------------------}
PROCEDURE WACHTEVENTJES;
VAR STARTTIJD:LONGINT;
    HUIDIGETIJD:LONGINT;
BEGIN
  STARTTIJD := TIJD;
  REPEAT
    HUIDIGETIJD := TIJD;
  UNTIL (HUIDIGETIJD > STARTTIJD+60) OR (HUIDIGETIJD < STARTTIJD);
END;

{---[speedloop (used during emulation for delay)]---------------------------}
{This procedure will be filled with bytes F8h (CLC) by SETUPSPEEDLOOP.      }
{It is now filled with 0's because all the F8h's take up some much space.   }
{Depending on various parameters, between every emulated 65C02 instruction,a}
{CALL will be made to this procedure in order to get the correct delay count}
{The shorter the wait period must be, the futher back in this procedure the }
{CALL address will be. This depends on the PC's CPU speed, the number of    }
{cycles that a 65C02 instruction should take and the number of cycles the PC}
{needs to emulate this instruction. This procedure is filled with CLC for   }
{four reasons: Firstly, it is a one-byte instruction; Secondly, it always   }
{takes 2 cycles, regardless the CPU type; thirdly, it is not pairable with  }
{the Pentium's V- nor U-pipe; therefore n CLCs always take n x 2 cycles; and}
{finally, the value of the carry flag is of no importance when calling this.}
{---------------------------------------------------------------------------}
PROCEDURE SPEEDLOOP; ASSEMBLER;
ASM;
{0}            DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
{1000}         DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
{2000}         DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
{3000}         DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
               DD    0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0, 0,0,0,0,0
END;

{---[setupspeedloop (fill up with CLC)]-------------------------------------}
PROCEDURE SETUPSPEEDLOOP; ASSEMBLER;
ASM;
               CLD
               MOV   AX,CS
               MOV   ES,AX
               MOV   DI,OFFSET SPEEDLOOP
               MOV   CX,+4000
               MOV   AL,$F8 {clc}
               REPZ
               STOSB
END;

{---[setcolors]-------------------------------------------------------------}
PROCEDURE SETCOLORS; ASSEMBLER;
ASM;
               PUSH  DS
               PUSH  DX
               PUSH  BX
               CLI
               MOV   AX,CS
               MOV   DS,AX
               MOV   SI,OFFSET EMULCOLORS
               SUB   BX,BX
@SETCOL1:      MOV   DX,$03C8
               MOV   AL,BL
               OUT   DX,AL
               INC   DX
               LODSB
               OUT   DX,AL
               LODSB
               OUT   DX,AL
               LODSB
               OUT   DX,AL
               INC   BL
               INC   BH
               CMP   BH,$10
               JB    @SETCOL1
               STI
               POP   BX
               POP   DX
               POP   DS
END;

{---[initatomgraph]---------------------------------------------------------}
PROCEDURE INITATOMGRAPH; ASSEMBLER;
ASM;
               MOV   AX,$0012
               INT   $10
               MOV   DX,$03D4
               MOV   AL,$09
               OUT   DX,AL
               INC   DX
               IN    AL,DX
               OR    AL,$80
               OUT   DX,AL {double scan active}
               MOV   DX,$03C4
               MOV   AL,$04
               OUT   DX,AL
               INC   DX
               IN    AL,DX
               OR    AL,$08
               OUT   DX,AL {chain 4 linear graphics mode}
               MOV   DX,$03D4
               MOV   AL,$14
               OUT   DX,AL
               INC   DX
               IN    AL,DX
               OR    AL,$40
               OUT   DX,AL {dword mode}
               DEC   DX
               MOV   AX,$0908
               OUT   DX,AX {preset rowscan: top border}
               MOV   AX,$2413
               OUT   DX,AX {logical screen line width}
               MOV   AL,$11
               OUT   DX,AL
               INC   DX
               IN    AL,DX
               AND   AL,$F0
               OR    AL,$09
               OUT   DX,AL {vertical retrace end}
               CALL  SETCOLORS
               MOV   AX,$1001
               MOV   BH,$07
               INT   $10
               MOV   BL,$00
@INITATGR1:    MOV   AX,$1000
               MOV   BH,BL
               PUSH  BX
               INT   $10
               POP   BX
               INC   BL
               CMP   BL,$10
               JNZ   @INITATGR1
               CLD
               MOV   AX,$A000
               MOV   ES,AX
               MOV   BYTE PTR [ES:$FFFF],$00
               SUB   DI,DI
               MOV   CX,$4000
@INITATGR2:    MOV   AX,$FFFF
               STOSW
               STOSB
               MOV   AL,$00
               STOSB
               LOOP  @INITATGR2
END;

{---[printstring; prints text after CALL and resumes execution after text]--}
PROCEDURE PRINTSTRING; ASSEMBLER;
ASM;
               PUSH  BP
               MOV   BP,SP
               MOV   SI,WORD PTR [SS:BP+$02]
               MOV   AL,BYTE PTR [CS:SI]
               INC   SI
               MOV   BYTE PTR [CS:CURSORX],AL
               MOV   AL,BYTE PTR [CS:SI]
               INC   SI
               MOV   BYTE PTR [CS:CURSORY],AL
               MOV   AL,BYTE PTR [CS:SI]
               INC   SI
               MOV   BL,AL
@PRINTSTR2:    MOV   AL,BYTE PTR [CS:SI]
               INC   SI
               AND   AL,$3F
               JZ    @PRINTSTR1
               CALL  PRINTCHAR
               JMP   @PRINTSTR2
@PRINTSTR1:    MOV   WORD PTR [SS:BP+$02],SI
               POP   BP
END;

{---[printbyte; AL=byte; BL=color]------------------------------------------}
PROCEDURE PRINTBYTE; ASSEMBLER;
ASM;
               PUSH  AX
               SHR   AL,4
               OR    AL,$30
               CMP   AL,$3A
               JB    @PRINTBYTE1
               SUB   AL,$39
@PRINTBYTE1:   CALL  PRINTCHAR
               POP   AX
               AND   AL,$0F
               OR    AL,$30
               CMP   AL,$3A
               JB    @PRINTBYTE2
               SUB   AL,$39
@PRINTBYTE2:   CALL  PRINTCHAR
END;

{---[printword; AX=word; BL=color]------------------------------------------}
PROCEDURE PRINTWORD; ASSEMBLER;
ASM;
               PUSH  AX
               MOV   AL,AH
               CALL  PRINTBYTE
               POP   AX
               CALL  PRINTBYTE
END;

{---[printdec]; AX=word; BL=color]------------------------------------------}
PROCEDURE PRINTDEC; ASSEMBLER;
ASM;
               MOV   CX,+10
               SUB   DX,DX
               DIV   CX
               OR    DL,$30
               MOV   BYTE PTR DECNUM[CS:$04],DL
               SUB   DX,DX
               DIV   CX
               OR    DL,$30
               MOV   BYTE PTR DECNUM[CS:$03],DL
               SUB   DX,DX
               DIV   CX
               OR    DL,$30
               MOV   BYTE PTR DECNUM[CS:$02],DL
               SUB   DX,DX
               DIV   CX
               OR    DL,$30
               MOV   BYTE PTR DECNUM[CS:$01],DL
               OR    AL,$30
               MOV   BYTE PTR DECNUM[CS:$00],AL
               MOV   BYTE PTR DECNUM[CS:$05],$00
@PRINTDEC2:    CMP   BYTE PTR DECNUM[CS:$00],'0'
               JNZ   @PRINTDEC1
               MOV   AX,WORD PTR DECNUM[CS:$01]
               MOV   WORD PTR DECNUM[CS:$00],AX
               MOV   AX,WORD PTR DECNUM[CS:$03]
               MOV   WORD PTR DECNUM[CS:$02],AX
               MOV   AL,BYTE PTR DECNUM[CS:$05]
               MOV   BYTE PTR DECNUM[CS:$04],AL
               JMP   @PRINTDEC2
@PRINTDEC1:    CMP   BYTE PTR DECNUM[CS:$00],$00
               JNZ   @PRINTDEC3
               MOV   BYTE PTR DECNUM[CS:$00],'0'
@PRINTDEC3:    PUSH  SI
               SUB   SI,SI
@PRINTDEC5:    MOV   AL,BYTE PTR DECNUM[CS:SI]
               OR    AL,AL
               JZ    @PRINTDEC4
               CALL  PRINTCHAR
               INC   SI
               JMP   @PRINTDEC5
@PRINTDEC4:    POP   SI
END;

{---[upperlines]------------------------------------------------------------}
PROCEDURE UPPERLINES; ASSEMBLER;
ASM;
               NOP
               SUB   AX,AX
               SUB   DI,DI
               MOV   CX,$4000
@UPPERL1:      MOV   AX,$00FF
               STOSW
               MOV   AX,$FFFF
               STOSW
               LOOP  @UPPERL1
               STI
               CALL  PRINTSTRING
               DB    +0,+0,$0F,'ACORN ATOM EMULATOR V1.33  BY WOUTER RAS'
               DB    'DISK  TAPE  OPTIONS  MONITOR',$00
               MOV   AL,'D' AND $3F
               MOV   BL,$09
               MOV   BYTE PTR [CS:CURSORX],+0
               MOV   BYTE PTR [CS:CURSORY],+1
               CALL  PRINTCHAR
               MOV   AL,'T' AND $3F
               MOV   BL,$09
               MOV   BYTE PTR [CS:CURSORX],+6
               CALL  PRINTCHAR
               MOV   AL,'O' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+12
               CALL  PRINTCHAR
               MOV   AL,'M' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+21
               CALL  PRINTCHAR
               MOV   AX,$FFFF
               MOV   DI,+9*$0120+$0140+12*4
               MOV   CX,+80
               REPZ
               STOSW
               MOV   DI,+19*$0120+$0140+12*4
               MOV   CX,+80
               REPZ
               STOSW
END;

{---[printdebugtxt]---------------------------------------------------------}
PROCEDURE PRINTDEBUGTXT; ASSEMBLER;
ASM;
               PUSH  DS
               PUSH  BX
               PUSH  CX
               PUSH  SI
               PUSH  DI
               MOV   AX,CS
               MOV   DS,AX
               MOV   SI,OFFSET DEBUGTXT
               MOV   DI,$0240
               MOV   CH,+17
@DBGMDON2:     MOV   CL,$04
@DBGMDON1:     MOV   WORD PTR [ES:DI],$00FF
               MOV   WORD PTR [ES:DI+$02],$FF00
               MOV   WORD PTR [ES:DI+$04],$00FF
               MOV   WORD PTR [ES:DI+$06],$FF00
               LODSB
               CALL  MAKEWIDER
               SUB   BX,BX
@DBGMDON3:     OR    BYTE PTR [ES:DI+BX],AH
               OR    BYTE PTR [ES:DI+$04+BX],AL
               INC   BL
               CMP   BL,$04
               JNZ   @DBGMDON3
               ADD   DI,+$08
               DEC   CL
               JNZ   @DBGMDON1
               ADD   DI,$0120-8*4
               DEC   CH
               JNZ   @DBGMDON2
               POP   DI
               POP   SI
               POP   CX
               POP   BX
               POP   DS
END;

{---[rebuildscreen]---------------------------------------------------------}
PROCEDURE REBUILDSCREEN; ASSEMBLER;
ASM;
               PUSHF
               CLI
               PUSH  BX
               PUSH  CX
               PUSH  DX
               MOV   BL,BYTE PTR [CS:GRAPHMODE]
               MOV   BH,$00
               SHL   BX,1
               MOV   CX,WORD PTR GRAPHTOP[CS:BX]
               MOV   DX,$8000
               SUB   CX,DX
               MOV   BX,WORD PTR UPDATETABLE[CS:BX]
@REBUILD1:     MOV   DI,DX
               CALL  BX
               INC   DX
               LOOP  @REBUILD1
               TEST  BYTE PTR [CS:BRKPNTON],$FF
               JZ    @REBUILD4
               CALL  PRINTDEBUGTXT
@REBUILD4:     POP   DX
               POP   CX
               POP   BX
               SUB   AX,AX
               MOV   WORD PTR [WACHTSCHULD],AX
               MOV   WORD PTR [PCCYCLES],AX
               POPF
END;

{---[keyreleasetel (byte)]--------------------------------------------------}
PROCEDURE KEYRELEASETEL; ASSEMBLER;
ASM;
END;

{---[keyrelease; BL=key#]---------------------------------------------------}
PROCEDURE KEYRELEASE; ASSEMBLER;
ASM;
               MOV   BH,$00
               MOV   BYTE PTR [CS:KEYRELEASETEL],$00
@KEYREL1:      CMP   BYTE PTR [CS:KEYRELEASETEL],+3
               JAE   @KEYREL2
               TEST  BYTE PTR TOETS[CS:BX],$03
               JNZ   @KEYREL1
@KEYREL2:
END;

{---[getcharcode (for usage in desktop)]------------------------------------}
PROCEDURE GETCHARCODE; ASSEMBLER;
ASM;
               NOP
               CLI   {shift,ctrl & alt not implemented yet}
               SUB   SI,SI
@CHARCODE2:    CMP   SI,$001D {---ctrl---}
               JZ    @CHARCODE7
               CMP   SI,$0038 {---alt---}
               JZ    @CHARCODE7
               CMP   SI,$002A {---left shift---}
               JZ    @CHARCODE7
               CMP   SI,$0036 {---right shift---}
               JZ    @CHARCODE7
               TEST  BYTE PTR TOETS[CS:SI],$03
               JNZ   @CHARCODE1
@CHARCODE7:    INC   SI
               CMP   SI,+$80
               JB    @CHARCODE2
@CHARCODE3:    STI
               PUSH  CX
               MOV   CX,$0800
@CHARCODE4:    DEC   CX
               JNZ   @CHARCODE4
               POP   CX
               JMP   GETCHARCODE
@CHARCODE1:    MOV   BYTE PTR TOETS[CS:SI],$80
               SHL   SI,1
               MOV   AX,WORD PTR BIOSCODE[CS:SI]
               CMP   AL,$FF
               JZ    @CHARCODE3
               TEST  BYTE PTR TOETS[CS:$2A],$03 {---left shift---}
               JNZ   @CHARCODE5
               TEST  BYTE PTR TOETS[CS:$36],$03 {---right shift---}
               JZ    @CHARCODE6
@CHARCODE5:    MOV   AL,AH
@CHARCODE6:    STI
END;

{---[inputword; ret carry clear if successful; AX=word]---------------------}
PROCEDURE INPUTWORD; ASSEMBLER;
ASM;
               MOV   BL,$0E
               MOV   AL,$7F
               CALL  PRINTCHAR
               SUB   BX,BX
@INPUTW2:      CALL  GETCHARCODE
               CMP   AL,$0D
               JZ    @INPUTW6
               CMP   AL,$1B
               JZ    @INPUTW7
               CMP   AL,$08
               JNZ   @INPUTW8
               OR    BL,BL
               JZ    @INPUTW2
               PUSH  BX
               DEC   BYTE PTR [CS:CURSORX]
               MOV   BL,$0E
               MOV   AL,' '
               CALL  PRINTCHAR
               SUB   BYTE PTR [CS:CURSORX],$02
               MOV   AL,$7F
               CALL  PRINTCHAR
               POP   BX
               DEC   BL
               JMP   @INPUTW2
@INPUTW8:      MOV   CL,AL
               CMP   AL,'0'
               JB    @INPUTW2
               CMP   AL,'9'
               JBE   @INPUTW5
               CMP   AL,'A'
               JB    @INPUTW2
               CMP   AL,'F'
               JA    @INPUTW2
               SUB   AL,$07
@INPUTW5:      SUB   AL,'0'
               CMP   BL,$04
               JAE   @INPUTW2
               MOV   BYTE PTR DECNUM[CS:BX],AL
               PUSH  BX
               DEC   BYTE PTR [CS:CURSORX]
               MOV   BL,$0E
               MOV   AL,CL
               AND   AL,$3F
               CALL  PRINTCHAR
               MOV   AL,$7F
               CALL  PRINTCHAR
               POP   BX
               INC   BL
               JMP   @INPUTW2
@INPUTW6:      OR    BL,BL
               JZ    @INPUTW7
               SUB   AX,AX
               SUB   DI,DI
@INPUTW10:     SHL   BYTE PTR DECNUM[CS:DI],4
               MOV   CX,$0004
@INPUTW9:      SHL   BYTE PTR DECNUM[CS:DI],1
               RCL   AX,1
               LOOP  @INPUTW9
               INC   DI
               DEC   BL
               JNZ   @INPUTW10
               CLC
               RETN
@INPUTW7:      TEST  BYTE PTR TOETS[CS:$01],$03
               JNZ   @INPUTW7
               STC
END;

{---[inputstring; CL=length; DS:DI-->buf; ret carry clear if successful]----}
PROCEDURE INPUTSTRING; ASSEMBLER;
ASM;
               PUSH  ES
               PUSH  DI
               PUSH  CX
               MOV   CH,$00
               MOV   AX,DS
               MOV   ES,AX
               MOV   AL,$00
               REPZ
               STOSB
               POP   CX
               POP   DI
               POP   ES
               MOV   BL,$0E
               MOV   AL,$7F
               CALL  PRINTCHAR
               SUB   BX,BX
@INPUTS2:      CALL  GETCHARCODE
               CMP   AL,$0D
               JZ    @INPUTS6
               CMP   AL,$1B
               JZ    @INPUTS7
               CMP   AL,$08
               JNZ   @INPUTS8
               OR    BL,BL
               JZ    @INPUTS2
               PUSH  BX
               DEC   BYTE PTR [CS:CURSORX]
               MOV   BL,$0E
               MOV   AL,' '
               CALL  PRINTCHAR
               SUB   BYTE PTR [CS:CURSORX],$02
               MOV   AL,$7F
               CALL  PRINTCHAR
               POP   BX
               DEC   BL
               JMP   @INPUTS2
@INPUTS8:      CMP   AL,' '
               JB    @INPUTS2
               CMP   AL,$60
               JAE   @INPUTS2
               CMP   BL,CL
               JAE   @INPUTS2
               MOV   BYTE PTR [DI+BX],AL
               PUSH  BX
               DEC   BYTE PTR [CS:CURSORX]
               MOV   BL,$0E
               AND   AL,$3F
               CALL  PRINTCHAR
               MOV   AL,$7F
               CALL  PRINTCHAR
               POP   BX
               INC   BL
               JMP   @INPUTS2
@INPUTS6:      OR    BL,BL
               JZ    @INPUTS7
@INPUTS3:      CMP   BL,CL
               JAE   @INPUTS1
               MOV   BYTE PTR [DI+BX],$00
               INC   BL
               JMP   @INPUTS3
@INPUTS1:      CLC
               RETN
@INPUTS7:      STC
END;

{---[checkexittape]---------------------------------------------------------}
PROCEDURE CHECKEXITTAPE; ASSEMBLER;
ASM;
               TEST  BYTE PTR TOETS[CS:$42],$03 {---f8---}
               JNZ   @TAPE93
               TEST  BYTE PTR TOETS[CS:$44],$03 {---f10---}
               JNZ   @TAPE91
               TEST  BYTE PTR TOETS[CS:$57],$03 {---f11---}
               JNZ   @TAPE92
               TEST  BYTE PTR TOETS[CS:$38],$03 {---alt---}
               JZ    @TAPE7
               TEST  BYTE PTR TOETS[CS:$18],$03 {---o---}
               JZ    @TAPE6
@TAPE91:       MOV   AL,$02
               RETN
@TAPE6:        TEST  BYTE PTR TOETS[CS:$32],$03 {---m---}
               JZ    @TAPE94
@TAPE92:       MOV   AL,$03
               RETN
@TAPE94:       TEST  BYTE PTR TOETS[CS:$20],$03 {---d---}
               JZ    @TAPE7
@TAPE93:       MOV   AL,$04
               RETN
@TAPE7:        TEST  BYTE PTR TOETS[CS:$01],$03 {---escape---}
               JZ    @TAPE8
               MOV   AL,$00
               RETN
@TAPE8:        MOV   AL,$FF
END;

{---[resetandload_ofs (word; holds offset for forward jump into main part)]-}
PROCEDURE RESETANDLOAD_OFS; ASSEMBLER;
ASM;
               DB    $00
END;

{---[lasttape (word)]-------------------------------------------------------}
PROCEDURE LASTTAPE; ASSEMBLER;
ASM;
               DW    $0000
END;

{---[vanaftape (word)]------------------------------------------------------}
PROCEDURE VANAFTAPE; ASSEMBLER;
ASM;
               DW    $0000
END;

{---[lastdisk (word)]-------------------------------------------------------}
PROCEDURE LASTDISK; ASSEMBLER;
ASM;
               DW    $0000
END;

{---[vanafdisk (word)]------------------------------------------------------}
PROCEDURE VANAFDISK; ASSEMBLER;
ASM;
               DW    $0000
END;

{---[vanafatm (word)]-------------------------------------------------------}
PROCEDURE VANAFATM; ASSEMBLER;
ASM;
               DW    $0000
END;

{---[lastatm (word)]--------------------------------------------------------}
PROCEDURE LASTATM; ASSEMBLER;
ASM;
               DW    $0000
END;

{---[vanafimp (word)]-------------------------------------------------------}
PROCEDURE VANAFIMP; ASSEMBLER;
ASM;
               DW    $0000
END;

{---[lastimp (word)]--------------------------------------------------------}
PROCEDURE LASTIMP; ASSEMBLER;
ASM;
               DW    $0000
END;

{---[importcode (word)]-----------------------------------------------------}
PROCEDURE IMPORTCODE; ASSEMBLER;
ASM;
               DW    $0000
END;

{---[showdir (AL=00:tape; AL=01:disk)]--------------------------------------}
PROCEDURE SHOWDIR; ASSEMBLER;
ASM;
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               OR    AL,AL
               JNZ   @SHOWDIR6
               MOV   AX,WORD PTR [CS:VANAFTAPE]
               MOV   BX,WORD PTR AANTALTAPEIMAGES
               MOV   CX,OFFSET TAPEIMAGES
               JMP   @SHOWDIR5
@SHOWDIR6:     MOV   AX,WORD PTR [CS:VANAFDISK]
               MOV   BX,WORD PTR AANTALDISKIMAGES
               MOV   CX,OFFSET DISKIMAGES
@SHOWDIR5:     MOV   WORD PTR @VANAF,AX
               MOV   WORD PTR @AANTALIMAGES,BX
               MOV   WORD PTR @OFSIMAGES,CX
               MOV   BYTE PTR [CS:CURSORY],+3
               MOV   AX,WORD PTR @VANAF
@SHOWDIR4:     PUSH  AX
               MOV   BYTE PTR [CS:CURSORX],+0
               CMP   AX,WORD PTR @AANTALIMAGES
               JAE   @SHOWDIR1
               MOV   CX,STR8GROOTTE
               MUL   CX
               ADD   AX,WORD PTR @OFSIMAGES
               MOV   SI,AX
               LODSB
               OR    AL,AL
               JZ    @SHOWDIR1
               MOV   AH,$00
               MOV   CX,AX
               MOV   BL,$0E
@SHOWDIR2:     LODSB
               AND   AL,$3F
               CALL  PRINTCHAR
               LOOP  @SHOWDIR2
@SHOWDIR1:     CMP   BYTE PTR [CS:CURSORX],+8
               JAE   @SHOWDIR3
               MOV   AL,' '
               CALL  PRINTCHAR
               JMP   @SHOWDIR1
@SHOWDIR3:     POP   AX
               INC   AX
               INC   BYTE PTR [CS:CURSORY]
               CMP   BYTE PTR [CS:CURSORY],+18
               JB    @SHOWDIR4
               MOV   AX,$FFFF
               MOV   DI,+(18*10-1)*$0120+$0140+12*4
               MOV   CX,+80
               REPZ
               STOSW
               POP   DS
               RETN
@VANAF:        DW    $0000
@AANTALIMAGES: DW    $0000
@OFSIMAGES:    DW    $0000
END;


{---[showatmfiles]----------------------------------------------------------}
PROCEDURE SHOWATMFILES; ASSEMBLER;
ASM;
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   BYTE PTR [CS:CURSORY],+3
               MOV   AX,WORD PTR [CS:VANAFATM]
@SHOWATM4:     PUSH  AX
               MOV   BYTE PTR [CS:CURSORX],+9
               CMP   AX,WORD PTR AANTALATOMFILES
               JAE   @SHOWATM6
               MOV   CX,ATMRECGROOTTE
               MUL   CX
               ADD   AX,OFFSET ATOMFILES
               MOV   SI,AX
               PUSH  SI
               MOV   CX,$0010
@SHOWATM2:     MOV   BL,$0E
               LODSB
               OR    AL,AL
               JZ    @SHOWATM1
               CMP   AL,'a'
               JB    @SHOWATM11
               CMP   AL,'z'
               JA    @SHOWATM11
               SUB   AL,'a'-'A'
               MOV   BL,$0C
@SHOWATM11:    AND   AL,$3F
               CALL  PRINTCHAR
               LOOP  @SHOWATM2
@SHOWATM1:     MOV   BL,$0E
               CMP   BYTE PTR [CS:CURSORX],+26
               JAE   @SHOWATM3
               MOV   AL,' '
               CALL  PRINTCHAR
               JMP   @SHOWATM1
@SHOWATM3:     POP   SI
               ADD   SI,+$10
               LODSW
               CMP   AX,$FFFF
               JZ    @SHOWATM8
@SHOWATM10:    CALL  PRINTWORD
               MOV   AL,' '
               CALL  PRINTCHAR
               LODSW
               CALL  PRINTWORD
               JMP   @SHOWATM9
@SHOWATM8:     CMP   WORD PTR [SI],$FFFC {not (freeze version)}
               JB    @SHOWATM10
               MOV   AL,'-'
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               MOV   AL,' '
               CALL  PRINTCHAR
               MOV   AL,'-'
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               ADD   SI,+$02
@SHOWATM9:     MOV   AL,' '
               CALL  PRINTCHAR
               LODSW
               CALL  PRINTWORD
               JMP   @SHOWATM5
@SHOWATM6:     MOV   CX,+31
               MOV   AL,' '
@SHOWATM7:     CALL  PRINTCHAR
               LOOP  @SHOWATM7
@SHOWATM5:     POP   AX
               INC   AX
               CMP   BYTE PTR [CS:CURSORY],+18
               JB    @SHOWATM4
               MOV   AX,$FFFF
               MOV   DI,+(18*10-1)*$0120+$0140+12*4
               MOV   CX,+80
               REPZ
               STOSW
               POP   DS
END;

{---[showimpfiles]----------------------------------------------------------}
PROCEDURE SHOWIMPFILES; ASSEMBLER;
ASM;
               MOV   AX,WORD PTR [CS:LASTIMP]
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               CMP   AX,WORD PTR AANTALIMPFILES
               POP   DS
               JBE   @SHOWIMP11
               SUB   AX,AX
               MOV   WORD PTR [CS:LASTIMP],AX
@SHOWIMP11:    CMP   AX,WORD PTR [CS:VANAFIMP]
               JAE   @SHOWIMP12
               MOV   WORD PTR [CS:VANAFIMP],AX
               JMP   @SHOWIMP13
@SHOWIMP12:    MOV   AX,WORD PTR [CS:VANAFIMP]
               ADD   AX,+15
               CMP   WORD PTR [CS:LASTIMP],AX
               JB    @SHOWIMP13
               INC   WORD PTR [CS:VANAFIMP]
               JMP   @SHOWIMP12
@SHOWIMP13:    PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   BYTE PTR [CS:CURSORY],+3
               MOV   AX,WORD PTR [CS:VANAFIMP]
@SHOWIMP4:     PUSH  AX
               MOV   BYTE PTR [CS:CURSORX],+9
               CMP   AX,WORD PTR AANTALIMPFILES
               JAE   @SHOWIMP6
               MOV   CX,ATMRECGROOTTE
               MUL   CX
               ADD   AX,OFFSET IMPFILES
               MOV   SI,AX
               PUSH  SI
               MOV   BL,$0E
               MOV   CX,$0010
@SHOWIMP2:     LODSB
               OR    AL,AL
               JZ    @SHOWIMP1
               AND   AL,$3F
               CALL  PRINTCHAR
               LOOP  @SHOWIMP2
@SHOWIMP1:     CMP   BYTE PTR [CS:CURSORX],+26
               JAE   @SHOWIMP3
               MOV   AL,' '
               CALL  PRINTCHAR
               JMP   @SHOWIMP1
@SHOWIMP3:     POP   SI
               ADD   SI,+$10
               LODSW
               CMP   AX,$FFFF
               JZ    @SHOWIMP8
@SHOWIMP10:    CALL  PRINTWORD
               MOV   AL,' '
               CALL  PRINTCHAR
               LODSW
               CALL  PRINTWORD
               JMP   @SHOWIMP9
@SHOWIMP8:     CMP   WORD PTR [SI],$FFFF
               JNZ   @SHOWIMP10
               MOV   AL,'-'
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               MOV   AL,' '
               CALL  PRINTCHAR
               MOV   AL,'-'
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               ADD   SI,+$02
@SHOWIMP9:     MOV   AL,' '
               CALL  PRINTCHAR
               LODSW
               CALL  PRINTWORD
               JMP   @SHOWIMP5
@SHOWIMP6:     MOV   CX,+31
               MOV   AL,' '
@SHOWIMP7:     CALL  PRINTCHAR
               LOOP  @SHOWIMP7
@SHOWIMP5:     POP   AX
               INC   AX
               CMP   BYTE PTR [CS:CURSORY],+18
               JB    @SHOWIMP4
               POP   DS
               MOV   AX,WORD PTR [CS:LASTIMP]
               SUB   AX,WORD PTR [CS:VANAFIMP]
               MOV   CX,+10*$0120
               MUL   CX
               ADD   AX,+30*$0120+$0140+12*4+9*4
               MOV   DI,AX
               MOV   CX,+31
               MOV   AL,$09
               CALL  XORPUT
               MOV   AX,$FFFF
               MOV   DI,+(18*10-1)*$0120+$0140+12*4
               MOV   CX,+80
               REPZ
               STOSW
END;

{---[bottomln2]-------------------------------------------------------------}
PROCEDURE BOTTOMLN2; ASSEMBLER;
ASM;
               MOV   AX,$FFFF
               MOV   DI,+(18*10-1)*$0120+$0140+12*4
               MOV   CX,+80
               REPZ
               STOSW
               MOV   DI,+20*$0120+$0140+12*4
               MOV   CX,+40
               MOV   AL,$0B
               CALL  XORPUT
END;

{---[tapebottomln]----------------------------------------------------------}
PROCEDURE TAPEBOTTOMLN; ASSEMBLER;
ASM;
               CMP   BYTE PTR [CS:TAPESCREEN],$00
               JNZ   @BOTTOMLN1
               CALL  PRINTSTRING
               DB    +0,+18,$0F,'OPEN  NEW                            ',$00
               MOV   AL,'O' AND $3F
               MOV   BL,$09
               MOV   BYTE PTR [CS:CURSORX],+0
               CALL  PRINTCHAR
               MOV   AL,'N' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+6
               CALL  PRINTCHAR
               JMP   BOTTOMLN2
@BOTTOMLN1:    CALL  PRINTSTRING
               DB    +0,+18,$0F,'SET LOAD REN IMPORT EXPORT DEL FREEZE',$00
               MOV   AL,'S' AND $3F
               MOV   BL,$09
               MOV   BYTE PTR [CS:CURSORX],+0
               CALL  PRINTCHAR
               MOV   AL,'L' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+4
               CALL  PRINTCHAR
               MOV   AL,'R' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+9
               CALL  PRINTCHAR
               MOV   AL,'I' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+13
               CALL  PRINTCHAR
               MOV   AL,'E' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+20
               CALL  PRINTCHAR
               MOV   AL,'D' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+27
               CALL  PRINTCHAR
               MOV   AL,'F' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+31
               CALL  PRINTCHAR
               JMP   BOTTOMLN2
END;

{---[newtapefile]-----------------------------------------------------------}
PROCEDURE NEWTAPEFILE; ASSEMBLER;
ASM;
               PUSH  ES
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,DS
               MOV   ES,AX
               MOV   AX,WORD PTR [CS:LASTTAPE]
               MOV   CX,STR8GROOTTE
               MUL   CX
               ADD   AX,OFFSET TAPEIMAGES
               MOV   SI,AX
               MOV   DI,OFFSET TAPEIMAGENAME
               MOV   CX,STR8GROOTTE
               REPZ
               MOVSB
               CALL  READFILESINTAPEIMAGE
               POP   DS
               POP   ES
               MOV   WORD PTR [CS:LASTATM],$0000
END;

{---[showall1tape]----------------------------------------------------------}
PROCEDURE SHOWALL1TAPE; ASSEMBLER;
ASM;
               MOV   AX,WORD PTR [CS:LASTTAPE]
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               CMP   AX,WORD PTR AANTALTAPEIMAGES
               POP   DS
               JBE   @SHOWALL7
               SUB   AX,AX
               MOV   WORD PTR [CS:LASTTAPE],AX
@SHOWALL7:     CMP   AX,WORD PTR [CS:VANAFTAPE]
               JAE   @SHOWALL3
               MOV   WORD PTR [CS:VANAFTAPE],AX
               JMP   @SHOWALL4
@SHOWALL3:     MOV   AX,WORD PTR [CS:VANAFTAPE]
               ADD   AX,+15
               CMP   WORD PTR [CS:LASTTAPE],AX
               JB    @SHOWALL4
               INC   WORD PTR [CS:VANAFTAPE]
               JMP   @SHOWALL3
@SHOWALL4:     MOV   AL,$00
               CALL  SHOWDIR
               MOV   AX,WORD PTR [CS:LASTTAPE]
               SUB   AX,WORD PTR [CS:VANAFTAPE]
               MOV   CX,+10*$0120
               MUL   CX
               ADD   AX,+30*$0120+$0140+12*4
               MOV   DI,AX
               MOV   CX,+8
               MOV   AL,$08
               CALL  XORPUT
END;

{---[showall2]--------------------------------------------------------------}
PROCEDURE SHOWALL2; ASSEMBLER;
ASM;
               MOV   AX,WORD PTR [CS:LASTATM]
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               CMP   AX,WORD PTR AANTALATOMFILES
               POP   DS
               JBE   @SHOWALL8
               SUB   AX,AX
               MOV   WORD PTR [CS:LASTATM],AX
@SHOWALL8:     CMP   AX,WORD PTR [CS:VANAFATM]
               JAE   @SHOWALL5
               MOV   WORD PTR [CS:VANAFATM],AX
               JMP   @SHOWALL6
@SHOWALL5:     MOV   AX,WORD PTR [CS:VANAFATM]
               ADD   AX,+15
               CMP   WORD PTR [CS:LASTATM],AX
               JB    @SHOWALL6
               INC   WORD PTR [CS:VANAFATM]
               JMP   @SHOWALL5
@SHOWALL6:     CALL  SHOWATMFILES
               CMP   BYTE PTR [CS:TAPESCREEN],$00
               JZ    @SHOWALL9
               MOV   AX,WORD PTR [CS:LASTATM]
               SUB   AX,WORD PTR [CS:VANAFATM]
               MOV   CX,+10*$0120
               MUL   CX
               ADD   AX,+30*$0120+$0140+12*4+9*4
               MOV   DI,AX
               MOV   CX,+31
               MOV   AL,$0A
               CALL  XORPUT
@SHOWALL9:
END;

{---[showall1disk]----------------------------------------------------------}
PROCEDURE SHOWALL1DISK; ASSEMBLER;
ASM;
               MOV   AX,WORD PTR [CS:LASTDISK]
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               CMP   AX,WORD PTR AANTALDISKIMAGES
               POP   DS
               JBE   @SHOWALL7
               SUB   AX,AX
               MOV   WORD PTR [CS:LASTDISK],AX
@SHOWALL7:     CMP   AX,WORD PTR [CS:VANAFDISK]
               JAE   @SHOWALL3
               MOV   WORD PTR [CS:VANAFDISK],AX
               JMP   @SHOWALL4
@SHOWALL3:     MOV   AX,WORD PTR [CS:VANAFDISK]
               ADD   AX,+15
               CMP   WORD PTR [CS:LASTDISK],AX
               JB    @SHOWALL4
               INC   WORD PTR [CS:VANAFDISK]
               JMP   @SHOWALL3
@SHOWALL4:     MOV   AL,$01
               CALL  SHOWDIR
               MOV   AX,WORD PTR [CS:LASTDISK]
               SUB   AX,WORD PTR [CS:VANAFDISK]
               MOV   CX,+10*$0120
               MUL   CX
               ADD   AX,+30*$0120+$0140+12*4
               MOV   DI,AX
               MOV   CX,+8
               MOV   AL,$09
               CALL  XORPUT
END;

{---[disk (desktop)]--------------------------------------------------------}
PROCEDURE DISK; ASSEMBLER;
ASM;
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   DI,+10*$0120+$0140+12*4
               MOV   CX,+4
               MOV   AL,$0B
               CALL  XORPUT
@DISK28:       MOV   DI,+20*$0120+$0140
               MOV   CX,+168*$0120/4
@DISK1:        MOV   AX,$00FF
               STOSW
               MOV   AX,$FFFF
               STOSW
               LOOP  @DISK1
               MOV   AX,CS
               MOV   DS,AX
               CALL  PRINTSTRING
               DB    +0,+18,$0F,'OPEN  NEW  SAVE  DRIVE          PROTECT',$00
               MOV   AL,'O' AND $3F
               MOV   BL,$09
               MOV   BYTE PTR [CS:CURSORX],+0
               MOV   BYTE PTR [CS:CURSORY],+18
               CALL  PRINTCHAR
               MOV   AL,'N' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+6
               CALL  PRINTCHAR
               MOV   AL,'S' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+11
               CALL  PRINTCHAR
               MOV   AL,'P' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+32
               CALL  PRINTCHAR
               CALL  PRINTSTRING
               DB    +23,+18,$09,'0 1 2 3',$00
               MOV   AX,$FFFF
               MOV   DI,+(18*10-1)*$0120+$0140+12*4
               MOV   CX,+80
               REPZ
               STOSW
               CALL  PRINTSTRING
               DB    +0,+2,$0C,'DISKIMG',$00
               MOV   DI,+20*$0120+12*4+8*4+$0140
               MOV   CX,+16*10-1
@DISK10:       AND   WORD PTR [ES:DI+$02],$FCFC
               ADD   DI,$0120
               LOOP  @DISK10
               MOV   AX,$FFFF
               MOV   DI,+29*$0120+$0140+12*4
               MOV   CX,+9
@DISK11:       STOSW
               INC   AX
               STOSW
               DEC   AX
               LOOP  @DISK11
               CALL  PRINTSTRING
               DB    +12,+5,$0C,'DRIVE 0:',$00
               CALL  PRINTSTRING
               DB    +12,+8,$0C,'DRIVE 1:',$00
               CALL  PRINTSTRING
               DB    +12,+11,$0C,'DRIVE 2:',$00
               CALL  PRINTSTRING
               DB    +12,+14,$0C,'DRIVE 3:',$00
               CALL  @XORPUTDRV
               MOV   AL,$01
               CALL  SHOWALL1DISK
               CALL  @SHOWDISKETTES
@DISK35:       MOV   AL,BYTE PTR TOETS[CS:$18] {---o---}
               OR    AL,BYTE PTR TOETS[CS:$1C] {---enter---}
               OR    AL,BYTE PTR TOETS[CS:$19] {---p---}
               AND   AL,$03
               JNZ   @DISK35
@DISK2:        TEST  BYTE PTR TOETS[CS:$0B],$03 {---0---}
               JZ    @DISK12
               CMP   BYTE PTR @DRIVE,$00
               JZ    @DISK12
               CALL  @XORPUTDRV
               MOV   BYTE PTR @DRIVE,$00
               CALL  @XORPUTDRV
               JMP   @DISK2
@DISK12:       MOV   BX,$0001
@DISK14:       TEST  BYTE PTR TOETS[CS:BX+$01],$03 {---1/2/3---}
               JZ    @DISK13
               CMP   BYTE PTR @DRIVE,BL
               JZ    @DISK13
               CALL  @XORPUTDRV
               MOV   BYTE PTR @DRIVE,BL
               CALL  @XORPUTDRV
               JMP   @DISK2
@DISK13:       INC   BL
               CMP   BL,$03
               JBE   @DISK14
               TEST  BYTE PTR TOETS[CS:$0F],$03 {---tab---}
               JZ    @DISK36
               MOV   AL,BYTE PTR TOETS[CS:$2A] {---left shift---}
               OR    AL,BYTE PTR TOETS[CS:$36] {---right shift---}
               AND   AL,$03
               JNZ   @DISK37
               CALL  @XORPUTDRV
               INC   BYTE PTR @DRIVE
@DISK39:       AND   BYTE PTR @DRIVE,$03
               CALL  @XORPUTDRV
               MOV   BL,$0F {---tab---}
               CALL  KEYRELEASE
               JMP   @DISK2
@DISK37:       CALL  @XORPUTDRV
               DEC   BYTE PTR @DRIVE
               JMP   @DISK39
@DISK36:       TEST  BYTE PTR TOETS[CS:$1F],$03 {---s---}
               JZ    @DISK15
               {---save ini-file---}
               CALL  PRINTSTRING
               DB    +24,+16,$0B,'WRITING INI-FILE',$00
               PUSH  ES
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               CALL  WRITEINIFILE
               POP   DS
               POP   ES
@DISK16:       TEST  BYTE PTR TOETS[CS:$1F],$03 {---s---}
               JNZ   @DISK16
               CALL  PRINTSTRING
               DB    +24,+16,$0B,'                ',$00
               JMP   @DISK2
@DISK15:       TEST  BYTE PTR TOETS[CS:$48],$03 {---up---}
               JZ    @DISK17
               CMP   WORD PTR [CS:LASTDISK],+$00
               JZ    @DISK2
               DEC   WORD PTR [CS:LASTDISK]
               MOV   AL,$01
               CALL  SHOWALL1DISK
               MOV   BL,$48 {---up---}
               CALL  KEYRELEASE
               JMP   @DISK2
@DISK17:       TEST  BYTE PTR TOETS[CS:$50],$03 {---down---}
               JZ    @DISK18
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR AANTALDISKIMAGES
               POP   DS
               CMP   WORD PTR [CS:LASTDISK],AX
               JAE   @DISK2
               INC   WORD PTR [CS:LASTDISK]
               MOV   AL,$01
               CALL  SHOWALL1DISK
               MOV   BL,$50 {---down---}
               CALL  KEYRELEASE
               JMP   @DISK2
@DISK18:       TEST  BYTE PTR TOETS[CS:$49],$03 {---page up---}
               JZ    @DISK20
               CMP   WORD PTR [CS:LASTDISK],+$00
               JZ    @DISK2
               SUB   WORD PTR [CS:LASTDISK],+14
               JNC   @DISK19
               MOV   WORD PTR [CS:LASTDISK],$0000
@DISK19:       MOV   AL,$01
               CALL  SHOWALL1DISK
               MOV   BL,$49 {---page up---}
               CALL  KEYRELEASE
               JMP   @DISK2
@DISK20:       TEST  BYTE PTR TOETS[CS:$51],$03 {---page down---}
               JZ    @DISK22
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR AANTALDISKIMAGES
               POP   DS
               CMP   WORD PTR [CS:LASTDISK],AX
               JAE   @DISK2
               ADD   WORD PTR [CS:LASTDISK],+14
               CMP   WORD PTR [CS:LASTDISK],AX
               JB    @DISK21
               MOV   WORD PTR [CS:LASTDISK],AX
@DISK21:       MOV   AL,$01
               CALL  SHOWALL1DISK
               MOV   BL,$51 {---page down---}
               CALL  KEYRELEASE
               JMP   @DISK2
@DISK22:       TEST  BYTE PTR TOETS[CS:$31],$03 {---n---}
               JZ    @DISK23
               MOV   BYTE PTR [CS:CURSORX],+11
               MOV   BYTE PTR [CS:CURSORY],+8
               MOV   BL,$09
               MOV   AL,01000101b
               CALL  PRINTCHAR
               MOV   CX,+16
               MOV   AL,01001100b
@DISK24:       CALL  PRINTCHAR
               LOOP  @DISK24
               MOV   AL,01001010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+11
               MOV   BYTE PTR [CS:CURSORY],+9
               MOV   AL,01010101b
               CALL  PRINTCHAR
               CALL  PRINTSTRING
               DB    +12,+9,$0C,' NEW DISK IMAGE ',$00
               MOV   BL,$09
               MOV   AL,01101010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+11
               MOV   BYTE PTR [CS:CURSORY],+10
               MOV   AL,01010101b
               CALL  PRINTCHAR
               MOV   CX,+16
               MOV   AL,' '
@DISK25:       CALL  PRINTCHAR
               LOOP  @DISK25
               MOV   AL,01101010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+11
               MOV   BYTE PTR [CS:CURSORY],+11
               MOV   AL,01010100b
               CALL  PRINTCHAR
               MOV   CX,+16
               MOV   AL,01001100b
@DISK26:       CALL  PRINTCHAR
               LOOP  @DISK26
               MOV   AL,01101000b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+16
               MOV   BYTE PTR [CS:CURSORY],+10
               MOV   BL,$31 {---n---}
               CALL  KEYRELEASE
               PUSH  DS
               MOV   AX,CS
               MOV   DS,AX
               MOV   DI,OFFSET FILENAMEBUF
               MOV   CL,$08
               CALL  INPUTSTRING
               POP   DS
               JC    @DISK27
               PUSH  ES
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               PUSH  CS {---segment of newname---}
               PUSH  OFFSET FILENAMEBUF {---offset of newname---}
               PUSH  CS {---segment of [CS:LASTDISK]---}
               PUSH  OFFSET [CS:LASTDISK] {---offset of [CS:LASTDISK]---}
               CALL  CREATEDISKFILE
               POP   DS
               POP   ES
@DISK27:       MOV   AL,BYTE PTR TOETS[CS:$01] {---escape---}
               OR    AL,BYTE PTR TOETS[CS:$1C] {---enter---}
               AND   AL,$03
               JNZ   @DISK27
               JMP   @DISK28
@DISK23:       TEST  BYTE PTR TOETS[CS:$38],$03 {---alt---}
               JNZ   @DISK29
               MOV   AL,BYTE PTR TOETS[CS:$18] {---o---}
               OR    AL,BYTE PTR TOETS[CS:$1C] {---enter---}
               AND   AL,$03
               JZ    @DISK29
               SUB   DI,DI
               MOV   AX,WORD PTR [CS:LASTDISK]
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               CMP   AX,WORD PTR AANTALDISKIMAGES
               POP   DS
               JZ    @DISK38
@DISK32:       MOV   BX,DI
               SHR   BL,1
               CMP   BL,BYTE PTR @DRIVE
               JZ    @DISK31
               PUSH  AX
               PUSH  DI
               CALL  @COMPAREDRIVE
               POP   DI
               POP   AX
               JZ    @DISK34
@DISK31:       ADD   DI,+$02
               CMP   DI,+$06
               JBE   @DISK32
               JMP   @DISK33
@DISK34:       CALL  ERRORSND
               JMP   @DISK28
@DISK38:       MOV   AL,BYTE PTR @DRIVE
               MOV   CL,+14
               MUL   CL
               MOV   DI,AX
               PUSH  DS
               PUSH  ES
               PUSHA
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   BYTE PTR DISKETTENAMES[DI],$00
               MOV   AL,BYTE PTR @DRIVE
               MOV   AH,$00
               PUSH  AX {drive#}
               CALL  CLOSE_DISK_IMAGE
               POPA
               POP   ES
               POP   DS
               JMP   @DISK28
@DISK33:       MOV   AL,BYTE PTR @DRIVE
               MOV   CL,+14
               MUL   CL
               MOV   DI,AX
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               CMP   BYTE PTR DISKETTENAMES[DI],$00
               POP   DS
               JZ    @DISK30
               PUSH  DS
               PUSH  ES
               PUSHA
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AL,BYTE PTR @DRIVE
               MOV   AH,$00
               PUSH  AX {drive#}
               CALL  CLOSE_DISK_IMAGE
               POPA
               POP   ES
               POP   DS
@DISK30:       PUSH  DS
               PUSH  ES
               PUSHA
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AL,BYTE PTR @DRIVE
               MOV   CL,+14
               MUL   CL
               MOV   BX,AX
               MOV   AX,WORD PTR [CS:LASTDISK]
               MOV   DI,AX
               SHL   AX,3
               ADD   AX,OFFSET DISKIMAGES
               ADD   DI,AX
               MOV   CX,+9
@DISK42:       MOV   AL,BYTE PTR [DI]
               MOV   BYTE PTR DISKETTENAMES[BX],AL
               INC   DI
               INC   BX
               LOOP  @DISK42
               CALL  COPYWRITEPROT
               MOV   CL,BYTE PTR @DRIVE
               MOV   CH,$00
               PUSH  CX {drive#}
               MOV   BL,CL
               AND   BX,$0001
               MOV   AL,BYTE PTR WRITEPROTECT[BX]
               AND   CL,$02
               SHL   CL,1
               SHR   AL,CL
               AND   AX,$0001
               PUSH  AX {read/write}
               CALL  OPEN_DISK_IMAGE
               POPA
               POP   ES
               POP   DS
               JMP   @DISK28
@DISK29:       TEST  BYTE PTR TOETS[CS:$19],$03 {---p---}
               JZ    @DISK40
               MOV   AL,BYTE PTR @DRIVE
               MOV   CL,+14
               MUL   CL
               MOV   BX,AX
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               CMP   BYTE PTR DISKETTENAMES[BX],$00
               POP   DS
               JZ    @DISK40
               PUSH  DS
               PUSH  ES
               PUSHA
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AL,BYTE PTR @DRIVE
               MOV   AH,$00
               PUSH  AX {drive#}
               CALL  CLOSE_DISK_IMAGE
               MOV   AL,BYTE PTR @DRIVE
               MOV   CL,+14
               MUL   CL
               ADD   AX,OFFSET DISKETTENAMES
               MOV   SI,AX
               LODSB
               MOV   DX,SI
               MOV   AH,$00
               ADD   SI,AX
               MOV   WORD PTR [SI],'D.'
               MOV   WORD PTR [SI+$02],'KS'
               MOV   BYTE PTR [SI+$04],$00
               MOV   AX,$4300
               PUSH  DX
               INT   $21 {---get file attributes---}
               POP   DX
               JC    @DISK41
               XOR   CL,READONLY {---toggle read only---}
               MOV   AX,$4301
               INT   $21 {---set file attributes---}
@DISK41:       CALL  COPYWRITEPROT
               MOV   CL,BYTE PTR @DRIVE
               MOV   CH,$00
               PUSH  CX {drive#}
               MOV   BL,CL
               AND   BX,$0001
               MOV   AL,BYTE PTR WRITEPROTECT[BX]
               AND   CL,$02
               SHL   CL,1
               SHR   AL,CL
               AND   AX,$0001
               PUSH  AX {read/write}
               CALL  OPEN_DISK_IMAGE
               POPA
               POP   ES
               POP   DS
               JMP   @DISK28
@DISK40:       TEST  BYTE PTR TOETS[CS:$43],$03 {---f9---}
               JNZ   @DISK3
               TEST  BYTE PTR TOETS[CS:$44],$03 {---f10---}
               JNZ   @DISK4
               TEST  BYTE PTR TOETS[CS:$57],$03 {---f11---}
               JNZ   @DISK5
               TEST  BYTE PTR TOETS[CS:$38],$03 {---alt---}
               JZ    @DISK6
               TEST  BYTE PTR TOETS[CS:$14],$03 {---t---}
               JZ    @DISK7
@DISK3:        MOV   AL,$01
               JMP   @DISK9
@DISK7:        TEST  BYTE PTR TOETS[CS:$18],$03 {---o---}
               JZ    @DISK8
@DISK4:        MOV   AL,$02
               JMP   @DISK9
@DISK8:        TEST  BYTE PTR TOETS[CS:$32],$03 {---m---}
               JZ    @DISK6
@DISK5:        MOV   AL,$03
               JMP   @DISK9
@DISK6:        TEST  BYTE PTR TOETS[CS:$01],$03 {---escape---}
               JZ    @DISK2
               MOV   AL,$00
@DISK9:        PUSH  AX
               MOV   DI,+10*$0120+$0140+12*4
               MOV   CX,+4
               MOV   AL,$0B
               CALL  XORPUT
               POP   AX
               RETN
@XORPUTDRV:    MOV   AL,BYTE PTR @DRIVE
               MOV   CL,+30
               MUL   CL
               MOV   CX,$0120
               MUL   CX
               ADD   AX,+50*$0120+$0140+92
               MOV   DI,AX
               MOV   AL,$0A
               MOV   CX,+25
               CALL  XORPUT
               RETN
@SHOWDISKETTES:CALL  @XORPUTDRV
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               SUB   DI,DI
@SHOWDSK1:     MOV   BYTE PTR [CS:CURSORX],+23
               MOV   AX,DI
               MOV   AH,AL
               SHL   AL,1
               ADD   AL,AH
               ADD   AL,+5
               MOV   BYTE PTR [CS:CURSORY],AL
               MOV   AX,DI
               MOV   CL,+14
               MUL   CL
               ADD   AX,OFFSET DISKETTENAMES
               MOV   SI,AX
               LODSB
               OR    AL,AL
               JZ    @SHOWDSK4
               MOV   CL,AL
@SHOWDSK3:     LODSB
               AND   AL,$3F
               MOV   BL,$0E
               CALL  PRINTCHAR
               DEC   CL
               JNZ   @SHOWDSK3
               MOV   CX,DI
               MOV   BL,CL
               AND   BX,$0001
               MOV   AL,BYTE PTR WRITEPROTECT[BX]
               AND   CL,$02
               SHL   CL,1
               SHR   AL,CL
               AND   AL,$01
               MOV   AL,' '
               JZ    @SHOWDSK7
               MOV   AL,'#'
@SHOWDSK7:     MOV   BYTE PTR [CS:CURSORX],+34
               MOV   BL,$0F
               CALL  PRINTCHAR
               JMP   @SHOWDSK2
@SHOWDSK4:     MOV   CX,$0008
@SHOWDSK5:     MOV   AL,'-'
               MOV   BL,$0E
               CALL  PRINTCHAR
               LOOP  @SHOWDSK5
@SHOWDSK2:     INC   DI
               CMP   DI,+$03
               JBE   @SHOWDSK1
               POP   DS
               CALL  @XORPUTDRV
               RETN
@COMPAREDRIVE: {---BL=drive; AX=index in diskimages---}
               PUSH  DS
               PUSH  ES
               MOV   DS,WORD PTR [CS:DATASEG]
               PUSH  DS
               POP   ES
               MOV   SI,AX
               SHL   AX,3
               ADD   AX,OFFSET DISKIMAGES
               ADD   SI,AX
               MOV   AL,BL
               MOV   CL,+14
               MUL   CL
               ADD   AX,OFFSET DISKETTENAMES
               MOV   DI,AX
               LODSB
               SCASB
               JNZ   @COMPDR1
               MOV   CL,AL
@COMPDR2:      CMPSB
               JNZ   @COMPDR1
               DEC   CL
               JNZ   @COMPDR2
@COMPDR1:      POP   ES
               POP   DS
               RETN
@DRIVE:        DB    $00
END;

{---[tape (desktop)]--------------------------------------------------------}
PROCEDURE TAPE; ASSEMBLER;
ASM;
               PUSH  DS
               PUSH  ES
               PUSHA
               MOV   DS,WORD PTR [CS:DATASEG]
               CALL  WRITEFOUTBUF
               POPA
               POP   ES
               POP   DS
               MOV   DI,+20*$0120+$0140
               MOV   CX,+168*$0120/4
@TAPE5:        MOV   AX,$00FF
               STOSW
               MOV   AX,$FFFF
               STOSW
               LOOP  @TAPE5
               MOV   DI,+10*$0120+$0140+12*4+6*4
               MOV   CX,4
               MOV   AL,$0B
               CALL  XORPUT
               CALL  PRINTSTRING
               DB    +0,+2,$0C,'TAPEIMG  ATOMFILE         STRT EXEC SIZE',$00
               MOV   DI,+20*$0120+12*4+8*4+$0140
               MOV   CX,+16*10-1
@TAPE9:        AND   WORD PTR [ES:DI+$02],$FCFC
               ADD   DI,$0120
               LOOP  @TAPE9
               MOV   AX,$FFFF
               MOV   DI,+29*$0120+$0140+12*4
               MOV   CX,+40
@TAPE2:        STOSW
               INC   AX
               STOSW
               DEC   AX
               LOOP  @TAPE2
               CMP   BYTE PTR [CS:TAPESCREEN],$00
               JNZ   @TAPE10
               MOV   DI,+20*$0120+$0140+12*4+9*4
               MOV   CX,+31
               JMP   @TAPE11
@TAPE10:       MOV   DI,+20*$0120+$0140+12*4
               MOV   CX,+9
@TAPE11:       MOV   AL,$0B
               CALL  XORPUT
               CALL  SHOWALL1TAPE
               CALL  SHOWALL2
@TAPE19:       CALL  TAPEBOTTOMLN
               CMP   BYTE PTR [CS:TAPESCREEN],$00
               JNZ   @TAPE12
@TAPE15:       {---cursor in directory screen---}
               TEST  BYTE PTR TOETS[CS:$48],$03 {---up---}
               JZ    @TAPE14
               CMP   WORD PTR [CS:LASTTAPE],+$00
               JZ    @TAPE15
               DEC   WORD PTR [CS:LASTTAPE]
               CALL  NEWTAPEFILE
               CALL  SHOWALL1TAPE
               CALL  SHOWALL2
               MOV   BL,$48 {---up---}
               CALL  KEYRELEASE
               JMP   @TAPE15
@TAPE14:       TEST  BYTE PTR TOETS[CS:$50],$03 {---down---}
               JZ    @TAPE13
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR AANTALTAPEIMAGES
               POP   DS
               CMP   WORD PTR [CS:LASTTAPE],AX
               JAE   @TAPE15
               INC   WORD PTR [CS:LASTTAPE]
               CALL  NEWTAPEFILE
               CALL  SHOWALL1TAPE
               CALL  SHOWALL2
               MOV   BL,$50 {---down---}
               CALL  KEYRELEASE
               JMP   @TAPE15
@TAPE13:       TEST  BYTE PTR TOETS[CS:$49],$03 {---page up---}
               JZ    @TAPE68
               CMP   WORD PTR [CS:LASTTAPE],+$00
               JZ    @TAPE15
               SUB   WORD PTR [CS:LASTTAPE],+14
               JNC   @TAPE67
               MOV   WORD PTR [CS:LASTTAPE],$0000
@TAPE67:       CALL  NEWTAPEFILE
               CALL  SHOWALL1TAPE
               CALL  SHOWALL2
               MOV   BL,$49 {---page up---}
               CALL  KEYRELEASE
               JMP   @TAPE15
@TAPE68:       TEST  BYTE PTR TOETS[CS:$51],$03 {---page down---}
               JZ    @TAPE69
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR AANTALTAPEIMAGES
               POP   DS
               CMP   WORD PTR [CS:LASTTAPE],AX
               JAE   @TAPE15
               ADD   WORD PTR [CS:LASTTAPE],+14
               CMP   WORD PTR [CS:LASTTAPE],AX
               JB    @TAPE70
               MOV   WORD PTR [CS:LASTTAPE],AX
@TAPE70:       CALL  NEWTAPEFILE
               CALL  SHOWALL1TAPE
               CALL  SHOWALL2
               MOV   BL,$51 {---page down---}
               CALL  KEYRELEASE
               JMP   @TAPE15
@TAPE69:       TEST  BYTE PTR TOETS[CS:$38],$03 {---alt---}
               JNZ   @TAPE18
               MOV   AL,BYTE PTR TOETS[CS:$18] {---o---}
               OR    AL,BYTE PTR TOETS[CS:$1C] {---enter---}
               OR    AL,BYTE PTR TOETS[CS:$4D] {---right---}
               AND   AL,$03
               JZ    @TAPE18
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR AANTALTAPEIMAGES
               POP   DS
               CMP   WORD PTR [CS:LASTTAPE],AX
               JAE   @TAPE15
               MOV   BYTE PTR [CS:TAPESCREEN],$01
               CALL  SHOWALL1TAPE
               CALL  SHOWALL2
@TAPE20:       MOV   BL,$1C {---enter---}
               CALL  KEYRELEASE
               JNZ   @TAPE20
               JMP   @TAPE19
@TAPE18:       TEST  BYTE PTR TOETS[CS:$31],$03 {---n---}
               JZ    @TAPE85
               MOV   BYTE PTR [CS:CURSORX],+11
               MOV   BYTE PTR [CS:CURSORY],+8
               MOV   BL,$09
               MOV   AL,01000101b
               CALL  PRINTCHAR
               MOV   CX,+16
               MOV   AL,01001100b
@TAPE86:       CALL  PRINTCHAR
               LOOP  @TAPE86
               MOV   AL,01001010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+11
               MOV   BYTE PTR [CS:CURSORY],+9
               MOV   AL,01010101b
               CALL  PRINTCHAR
               CALL  PRINTSTRING
               DB    +12,+9,$0C,' NEW TAPE IMAGE ',$00
               MOV   BL,$09
               MOV   AL,01101010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+11
               MOV   BYTE PTR [CS:CURSORY],+10
               MOV   AL,01010101b
               CALL  PRINTCHAR
               MOV   CX,+16
               MOV   AL,' '
@TAPE87:       CALL  PRINTCHAR
               LOOP  @TAPE87
               MOV   AL,01101010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+11
               MOV   BYTE PTR [CS:CURSORY],+11
               MOV   AL,01010100b
               CALL  PRINTCHAR
               MOV   CX,+16
               MOV   AL,01001100b
@TAPE88:       CALL  PRINTCHAR
               LOOP  @TAPE88
               MOV   AL,01101000b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+16
               MOV   BYTE PTR [CS:CURSORY],+10
               MOV   BL,$31 {---n---}
               CALL  KEYRELEASE
               PUSH  DS
               MOV   AX,CS
               MOV   DS,AX
               MOV   DI,OFFSET FILENAMEBUF
               MOV   CL,$08
               CALL  INPUTSTRING
               POP   DS
               JC    @TAPE89
               PUSH  ES
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               PUSH  CS {---segment of newname---}
               PUSH  OFFSET FILENAMEBUF {---offset of newname---}
               PUSH  CS {---segment of [CS:LASTTAPE]---}
               PUSH  OFFSET [CS:LASTTAPE] {---offset of [CS:LASTTAPE]---}
               CALL  CREATETAPEFILE
               POP   DS
               POP   ES
@TAPE89:       CALL  SHOWALL1TAPE
               CALL  SHOWALL2
@TAPE90:       MOV   AL,BYTE PTR TOETS[CS:$01] {---escape---}
               OR    AL,BYTE PTR TOETS[CS:$1C] {---enter---}
               AND   AL,$03
               JNZ   @TAPE90
               JMP   @TAPE15
@TAPE85:       CALL  CHECKEXITTAPE
               CMP   AL,$FF
               JZ    @TAPE15
               PUSH  AX
               MOV   DI,+10*$0120+$0140+12*4+6*4
               MOV   CX,4
               MOV   AL,$0B
               CALL  XORPUT
               POP   AX
               RETN
@TAPE12:       {---cursor in atom files screen---}
               TEST  BYTE PTR TOETS[CS:$48],$03 {---up---}
               JZ    @TAPE21
               CMP   WORD PTR [CS:LASTATM],+$00
               JZ    @TAPE12
               DEC   WORD PTR [CS:LASTATM]
               CALL  SHOWALL2
               MOV   BL,$48 {---up---}
               CALL  KEYRELEASE
               JMP   @TAPE12
@TAPE21:       TEST  BYTE PTR TOETS[CS:$50],$03 {---down---}
               JZ    @TAPE23
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR AANTALATOMFILES
               POP   DS
               CMP   WORD PTR [CS:LASTATM],AX
               JAE   @TAPE12
               INC   WORD PTR [CS:LASTATM]
               CALL  SHOWALL2
               MOV   BL,$50 {---down---}
               CALL  KEYRELEASE
               JMP   @TAPE12
@TAPE23:       TEST  BYTE PTR TOETS[CS:$49],$03 {---page up---}
               JZ    @TAPE27
               CMP   WORD PTR [CS:LASTATM],+$00
               JZ    @TAPE12
               SUB   WORD PTR [CS:LASTATM],+14
               JNC   @TAPE29
               MOV   WORD PTR [CS:LASTATM],$0000
@TAPE29:       CALL  SHOWALL2
               MOV   BL,$49 {---page up---}
               CALL  KEYRELEASE
               JMP   @TAPE12
@TAPE27:       TEST  BYTE PTR TOETS[CS:$51],$03 {---page down---}
               JZ    @TAPE28
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR AANTALATOMFILES
               POP   DS
               CMP   WORD PTR [CS:LASTATM],AX
               JAE   @TAPE12
               ADD   WORD PTR [CS:LASTATM],+14
               CMP   WORD PTR [CS:LASTATM],AX
               JB    @TAPE31
               MOV   WORD PTR [CS:LASTATM],AX
@TAPE31:       CALL  SHOWALL2
               MOV   BL,$51 {---page down---}
               CALL  KEYRELEASE
               JMP   @TAPE12
@TAPE28:       TEST  BYTE PTR TOETS[CS:$38],$03 {---alt---}
               JNZ   @TAPE25
               MOV   AL,BYTE PTR TOETS[CS:$14] {---t---}
               OR    AL,BYTE PTR TOETS[CS:$4B] {---left---}
               AND   AL,$03
               JZ    @TAPE25
               MOV   BYTE PTR [CS:TAPESCREEN],$00
               CALL  SHOWALL1TAPE
               CALL  SHOWALL2
               JMP   @TAPE19
@TAPE25:       TEST  BYTE PTR TOETS[CS:$26],$03 {---l---}
               JZ    @TAPE33
               TEST  BYTE PTR [CS:BRKPNTON],$FF
               JNZ   @TAPE33
               PUSH  ES
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   ES,WORD PTR [CS:ATOMSEG]
               MOV   AX,WORD PTR [CS:LASTATM]
               CMP   AX,WORD PTR AANTALATOMFILES
               JB    @TAPE38
               SUB   AX,AX
               MOV   WORD PTR [CS:LASTATM],AX
@TAPE38:       MOV   CX,ATMRECGROOTTE
               MUL   CX
               ADD   AX,OFFSET ATOMFILES
               MOV   SI,AX
               MOV   DI,$0100
               CMP   WORD PTR [SI+$0010],$2900
               JNZ   @TAPE36
               CMP   WORD PTR [SI+$0012],$C2B2
               JNZ   @TAPE54
               MOV   AL,'L'
               STOSB
               MOV   AL,'O'
               JMP   @TAPE37
@TAPE36:       CMP   WORD PTR [SI+$0012],$C2B2
               JNZ   @TAPE54
               MOV   AL,'*'
               STOSB
               MOV   AL,'L'
               JMP   @TAPE37
@TAPE54:       MOV   AL,'*'
               STOSB
               MOV   AL,'R'
@TAPE37:       STOSB
               MOV   AL,'.'
               STOSB
               MOV   AL,'"'
               STOSB
               MOV   CX,$0010
@TAPE34:       LODSB
               OR    AL,AL
               JZ    @TAPE35
               STOSB
               LOOP  @TAPE34
@TAPE35:       MOV   AL,'"'
               STOSB
               MOV   AL,$0D
               STOSB
               MOV   AL,$0A
               STOSB
               POP   DS
               POP   ES
               ADD   SP,+$04 {call TAPE and call @SHOWMENU}
               JMP   WORD PTR [CS:RESETANDLOAD_OFS]
@TAPE33:       MOV   AL,BYTE PTR TOETS[CS:$1F] {---s---}
               OR    AL,BYTE PTR TOETS[CS:$1C] {---enter---}
               AND   AL,$03
               JZ    @TAPE39
@TAPE40:       MOV   AL,BYTE PTR TOETS[CS:$1F] {---s---}
               OR    AL,BYTE PTR TOETS[CS:$1C] {---enter---}
               AND   AL,$03
               JNZ   @TAPE40
               MOV   AL,$00
               RETN
@TAPE39:       TEST  BYTE PTR TOETS[CS:$21],$03 {---f---}
               JZ    @TAPE16
               PUSH  ES
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               CALL  FREEZE
               MOV   AX,WORD PTR AANTALATOMFILES
               MOV   WORD PTR [CS:LASTATM],AX
               POP   DS
               POP   ES
               CALL  SHOWALL1TAPE
               CALL  SHOWALL2
               MOV   BL,$21 {---f---}
               CALL  KEYRELEASE
               JMP   @TAPE12
@TAPE16:       TEST  BYTE PTR TOETS[CS:$20],$FF {---d---}
               JZ    @TAPE41
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR AANTALATOMFILES
               POP   DS
               CMP   WORD PTR [CS:LASTATM],AX
               JAE   @TAPE41
               MOV   BYTE PTR [CS:CURSORX],+10
               MOV   BYTE PTR [CS:CURSORY],+7
               MOV   BL,$09
               MOV   AL,01000101b
               CALL  PRINTCHAR
               MOV   CX,+18
               MOV   AL,01001100b
@TAPE42:       CALL  PRINTCHAR
               LOOP  @TAPE42
               MOV   AL,01001010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+10
               MOV   BYTE PTR [CS:CURSORY],+8
               MOV   AL,01010101b
               CALL  PRINTCHAR
               CALL  PRINTSTRING
               DB    +11,+8,$0E,'   DELETE FILE:   ',$00
               MOV   BL,$09
               MOV   AL,01101010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+10
               MOV   BYTE PTR [CS:CURSORY],+9
               MOV   AL,01010101b
               CALL  PRINTCHAR
               MOV   AL,' '
               CALL  PRINTCHAR
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR [CS:LASTATM]
               MOV   CX,ATMRECGROOTTE
               MUL   CX
               ADD   AX,OFFSET ATOMFILES
               MOV   SI,AX
               SUB   BX,BX
@TAPE45:       CMP   BYTE PTR [SI+BX],$00
               JZ    @TAPE44
               INC   BL
               CMP   BL,$10
               JB    @TAPE45
@TAPE44:       SHR   BL,1
               PUSHF
               ADC   BL,$00
               MOV   CH,$00
               MOV   CL,$08
               SUB   CL,BL
               PUSH  CX
               JZ    @TAPE84
               MOV   AL,' '
@TAPE46:       CALL  PRINTCHAR
               LOOP  @TAPE46
@TAPE84:       MOV   CL,$10
@TAPE48:       LODSB
               OR    AL,AL
               JZ    @TAPE47
               AND   AL,$3F
               MOV   BL,$09
               CALL  PRINTCHAR
               LOOP  @TAPE48
@TAPE47:       POP   CX
               POPF
               ADC   CL,$00
               INC   CL
               MOV   AL,' '
@TAPE49:       CALL  PRINTCHAR
               LOOP  @TAPE49
               POP   DS
               MOV   BL,$09
               MOV   AL,01101010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+10
               MOV   BYTE PTR [CS:CURSORY],+10
               MOV   AL,01010101b
               CALL  PRINTCHAR
               CALL  PRINTSTRING
               DB    +11,+10,$0C,'    YES OR NO?    ',$00
               MOV   BL,$09
               MOV   AL,01101010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+10
               MOV   BYTE PTR [CS:CURSORY],+11
               MOV   AL,01010100b
               CALL  PRINTCHAR
               MOV   CX,+18
               MOV   AL,01001100b
@TAPE43:       CALL  PRINTCHAR
               LOOP  @TAPE43
               MOV   AL,01101000b
               CALL  PRINTCHAR
@TAPE50:       MOV   AL,BYTE PTR TOETS[CS:$01] {---escape---}
               OR    AL,BYTE PTR TOETS[CS:$15] {---y---}
               OR    AL,BYTE PTR TOETS[CS:$31] {---n---}
               AND   AL,$03
               JNZ   @TAPE50
@TAPE52:       MOV   AL,BYTE PTR TOETS[CS:$01] {---escape---}
               OR    AL,BYTE PTR TOETS[CS:$31] {---n---}
               AND   AL,$03
               JNZ   @TAPE51
               TEST  BYTE PTR TOETS[CS:$15],$03 {---y---}
               JZ    @TAPE52
               PUSH  ES
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               PUSH  WORD PTR [CS:LASTATM] {---filenumber to be deleted---}
               CALL  DELETEFILE
               POP   DS
               POP   ES
@TAPE51:       CALL  SHOWALL1TAPE
               CALL  SHOWALL2
@TAPE53:       MOV   AL,BYTE PTR TOETS[CS:$01] {---escape---}
               OR    AL,BYTE PTR TOETS[CS:$15] {---y---}
               OR    AL,BYTE PTR TOETS[CS:$31] {---n---}
               AND   AL,$03
               JNZ   @TAPE53
               JMP   @TAPE12
@TAPE41:       TEST  BYTE PTR TOETS[CS:$12],$03 {---e---}
               JZ    @TAPE55
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR AANTALATOMFILES
               POP   DS
               CMP   WORD PTR [CS:LASTATM],AX
               JAE   @TAPE55
               PUSH  ES
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               PUSH  WORD PTR [CS:LASTATM] {---filenumber to be exported---}
               CALL  EXPORT
               POP   DS
               POP   ES
               MOV   BL,$12 {---e---}
               CALL  KEYRELEASE
               JMP   @TAPE12
@TAPE55:       TEST  BYTE PTR TOETS[CS:$17],$03 {---i---}
               JZ    @TAPE56
               CALL  PRINTSTRING
               DB    +0,+18,$0F,'SELECT                               ',$00
               MOV   AL,'S' AND $3F
               MOV   BL,$09
               MOV   BYTE PTR [CS:CURSORX],+0
               CALL  PRINTCHAR
               PUSH  ES
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               CALL  READIMPORTABLEFILES
               POP   DS
               POP   ES
               MOV   WORD PTR [CS:LASTIMP],$0000
               CALL  SHOWIMPFILES
@TAPE57:       TEST  BYTE PTR TOETS[CS:$48],$03 {---up---}
               JZ    @TAPE58
               CMP   WORD PTR [CS:LASTIMP],+$00
               JZ    @TAPE57
               DEC   WORD PTR [CS:LASTIMP]
               CALL  SHOWIMPFILES
               MOV   BL,$48 {---up---}
               CALL  KEYRELEASE
               JMP   @TAPE57
@TAPE58:       TEST  BYTE PTR TOETS[CS:$50],$03 {---down---}
               JZ    @TAPE59
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR AANTALIMPFILES
               POP   DS
               CMP   WORD PTR [CS:LASTIMP],AX
               JAE   @TAPE57
               INC   WORD PTR [CS:LASTIMP]
               CALL  SHOWIMPFILES
               MOV   BL,$50 {---down---}
               CALL  KEYRELEASE
               JMP   @TAPE57
@TAPE59:       TEST  BYTE PTR TOETS[CS:$49],$03 {---page up---}
               JZ    @TAPE60
               CMP   WORD PTR [CS:LASTIMP],+$00
               JZ    @TAPE57
               SUB   WORD PTR [CS:LASTIMP],+14
               JNC   @TAPE61
               MOV   WORD PTR [CS:LASTIMP],$0000
@TAPE61:       CALL  SHOWIMPFILES
               MOV   BL,$49 {---page up---}
               CALL  KEYRELEASE
               JMP   @TAPE57
@TAPE60:       TEST  BYTE PTR TOETS[CS:$51],$03 {---page down---}
               JZ    @TAPE62
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR AANTALIMPFILES
               POP   DS
               CMP   WORD PTR [CS:LASTIMP],AX
               JAE   @TAPE57
               ADD   WORD PTR [CS:LASTIMP],+14
               CMP   WORD PTR [CS:LASTIMP],AX
               JB    @TAPE63
               MOV   WORD PTR [CS:LASTIMP],AX
@TAPE63:       CALL  SHOWIMPFILES
               MOV   BL,$51 {---page down---}
               CALL  KEYRELEASE
               JMP   @TAPE57
@TAPE62:       TEST  BYTE PTR TOETS[CS:$01],$03
               JZ    @TAPE64
@TAPE65:       TEST  BYTE PTR TOETS[CS:$01],$03
               JNZ   @TAPE65
               CALL  SHOWALL2
               CALL  BOTTOMLN2
               JMP   @TAPE19
@TAPE64:       MOV   AL,BYTE PTR TOETS[CS:$1F] {---s---}
               OR    AL,BYTE PTR TOETS[CS:$1C] {---enter---}
               AND   AL,$03
               JZ    @TAPE57
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR AANTALIMPFILES
               POP   DS
               CMP   WORD PTR [CS:LASTIMP],AX
               JAE   @TAPE57
               PUSH  ES
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               PUSH  WORD PTR [CS:LASTATM] {---filepointer:where to import---}
               PUSH  WORD PTR [CS:LASTIMP] {---file to be imported---}
               PUSH  CS {---segment exitcode---}
               PUSH  OFFSET [CS:IMPORTCODE] {---offset exitcode---}
               CALL  IMPORT
               POP   DS
               POP   ES
               TEST  WORD PTR [CS:IMPORTCODE],$8000
               JNZ   @TAPE66
               INC   WORD PTR [CS:LASTATM]
@TAPE66:       MOV   AL,BYTE PTR TOETS[CS:$1F] {---s---}
               OR    AL,BYTE PTR TOETS[CS:$1C] {---enter---}
               AND   AL,$03
               JNZ   @TAPE66
               CALL  SHOWALL2
               CALL  BOTTOMLN2
               JMP   @TAPE19
@TAPE56:       TEST  BYTE PTR TOETS[CS:$13],$03 {---r---}
               JZ    @TAPE71
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR AANTALATOMFILES
               POP   DS
               CMP   WORD PTR [CS:LASTATM],AX
               JAE   @TAPE71
               MOV   BYTE PTR [CS:CURSORX],+10
               MOV   BYTE PTR [CS:CURSORY],+7
               MOV   BL,$09
               MOV   AL,01000101b
               CALL  PRINTCHAR
               MOV   CX,+18
               MOV   AL,01001100b
@TAPE72:       CALL  PRINTCHAR
               LOOP  @TAPE72
               MOV   AL,01001010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+10
               MOV   BYTE PTR [CS:CURSORY],+8
               MOV   AL,01010101b
               CALL  PRINTCHAR
               CALL  PRINTSTRING
               DB    +11,+8,$0E,'   RENAME FILE:   ',$00
               MOV   BL,$09
               MOV   AL,01101010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+10
               MOV   BYTE PTR [CS:CURSORY],+9
               MOV   AL,01010101b
               CALL  PRINTCHAR
               MOV   AL,' '
               CALL  PRINTCHAR
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   AX,WORD PTR [CS:LASTATM]
               MOV   CX,ATMRECGROOTTE
               MUL   CX
               ADD   AX,OFFSET ATOMFILES
               MOV   SI,AX
               SUB   BX,BX
@TAPE75:       CMP   BYTE PTR [SI+BX],$00
               JZ    @TAPE74
               INC   BL
               CMP   BL,$10
               JB    @TAPE75
@TAPE74:       SHR   BL,1
               PUSHF
               ADC   BL,$00
               MOV   CH,$00
               MOV   CL,$08
               SUB   CL,BL
               PUSH  CX
               JZ    @TAPE83
               MOV   AL,' '
@TAPE76:       CALL  PRINTCHAR
               LOOP  @TAPE76
@TAPE83:       MOV   CL,$10
@TAPE78:       LODSB
               OR    AL,AL
               JZ    @TAPE77
               AND   AL,$3F
               MOV   BL,$09
               CALL  PRINTCHAR
               LOOP  @TAPE78
@TAPE77:       POP   CX
               POPF
               ADC   CL,$00
               INC   CL
               MOV   AL,' '
@TAPE79:       CALL  PRINTCHAR
               LOOP  @TAPE79
               POP   DS
               MOV   BL,$09
               MOV   AL,01101010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+10
               MOV   BYTE PTR [CS:CURSORY],+10
               MOV   AL,01010101b
               CALL  PRINTCHAR
               MOV   CX,$12
               MOV   AL,' '
@TAPE81:       CALL  PRINTCHAR
               LOOP  @TAPE81
               MOV   AL,01101010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+10
               MOV   BYTE PTR [CS:CURSORY],+11
               MOV   AL,01010100b
               CALL  PRINTCHAR
               MOV   CX,+18
               MOV   AL,01001100b
@TAPE73:       CALL  PRINTCHAR
               LOOP  @TAPE73
               MOV   AL,01101000b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+12
               MOV   BYTE PTR [CS:CURSORY],+10
               MOV   BL,$13 {---r---}
               CALL  KEYRELEASE
               PUSH  DS
               MOV   AX,CS
               MOV   DS,AX
               MOV   DI,OFFSET FILENAMEBUF
               MOV   CL,$10
               CALL  INPUTSTRING
               POP   DS
               JC    @TAPE82
               PUSH  ES
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               PUSH  WORD PTR [CS:LASTATM] {---filepointer---}
               PUSH  CS {---segment of newname---}
               PUSH  OFFSET FILENAMEBUF {---offset of newname---}
               CALL  RENAMEFILE
               POP   DS
               POP   ES
@TAPE82:       CALL  SHOWALL1TAPE
               CALL  SHOWALL2
@TAPE80:       MOV   AL,BYTE PTR TOETS[CS:$01] {---escape---}
               OR    AL,BYTE PTR TOETS[CS:$1C] {---enter---}
               AND   AL,$03
               JNZ   @TAPE80
               JMP   @TAPE12
@TAPE71:       CALL  CHECKEXITTAPE
               CMP   AL,$FF
               JZ    @TAPE12
               PUSH  AX
               MOV   DI,+10*$0120+$0140+12*4+6*4
               MOV   CX,4
               MOV   AL,$0B
               CALL  XORPUT
               POP   AX
               RETN
@FOUTEXITCODE: DW    $0000
END;

{---[optcurs (byte)]--------------------------------------------------------}
PROCEDURE OPTCURS; ASSEMBLER;
ASM;
               DB    $00
END;

{---[xorputoptcurs]---------------------------------------------------------}
PROCEDURE XORPUTOPTCURS; ASSEMBLER;
ASM;
               MOV   BL,BYTE PTR [CS:OPTCURS]
               MOV   BH,$00
               MOV   AL,BYTE PTR @OPTYTABLE[CS:BX]
               MOV   AH,$00
               MOV   CX,+10*$0120
               MUL   CX
               ADD   AX,+$0140+12*4
               MOV   DI,AX
               MOV   AL,BYTE PTR @OPTXTABLE[CS:BX]
               MOV   AH,$00
               SHL   AX,2
               ADD   DI,AX
               MOV   CL,BYTE PTR @OPTLTABLE[CS:BX]
               MOV   CH,$00
               MOV   AL,$0B
               CALL  XORPUT
               RETN
@OPTXTABLE:    DB     0, 0,24,24, 7,10,13, 7,10,13, 7,10,13, 7,10,13
               DB     7,10,13, 7,10,13, 7,10,13,24, 0, 0
@OPTYTABLE:    DB     3, 4, 3, 4, 7, 7, 7, 8, 8, 8, 9, 9, 9,10,10,10
               DB    11,11,11,12,12,12,13,13,13,15,16,17
@OPTLTABLE:    DB    12,12,14,14, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2
               DB     2, 2, 2, 2, 2, 2, 2, 2, 2,12, 7, 7
END;

{---[options (desktop)]-----------------------------------------------------}
PROCEDURE OPTIONS; ASSEMBLER;
ASM;
               MOV   DI,+20*$0120+$0140
               MOV   CX,+168*$0120/4
@OPT3:         MOV   AX,$00FF
               STOSW
               MOV   AX,$FFFF
               STOSW
               LOOP  @OPT3
               MOV   DI,+10*$0120+$0140+12*4+12*4
               MOV   CX,+7
               MOV   AL,$0B
               CALL  XORPUT
               MOV   AX,CS
               MOV   DS,AX
               CALL  PRINTSTRING
               DB    +0,+2,$0C,'CPU SPEED',$00
               CALL  PRINTSTRING
               DB    +0,+3,$0E,'( ) ORIGINAL            ( ) ACORN ATOM',$00
               CALL  PRINTSTRING
               DB    +0,+4,$0E,'( ) MAXIMUM             ( ) REGULAR',$00
               CALL  PRINTSTRING
               DB    +24,+2,$0C,'ASSEMBLER LAYOUT',$00
               CALL  PRINTSTRING
               DB    +0,+6,$0C,'COLORS DURING EMULATION',$00
               CALL  PRINTSTRING
               DB    +0,+7,$0F,'BACKGR',$00
               CALL  PRINTSTRING
               DB    +0,+8,$0F,'FOREGR',$00
               CALL  PRINTSTRING
               DB    +0,+9,$0F,'GREYSB',$00
               CALL  PRINTSTRING
               DB    +0,+10,$0F,'COLOR0',$00
               CALL  PRINTSTRING
               DB    +0,+11,$0F,'COLOR1',$00
               CALL  PRINTSTRING
               DB    +0,+12,$0F,'COLOR2',$00
               CALL  PRINTSTRING
               DB    +0,+13,$0F,'COLOR3',$00
               CALL  PRINTSTRING
               DB    +0,+15,$0C,'SOUND OUTPUT',$00
               CALL  PRINTSTRING
               DB    +0,+16,$0E,'( ) YES',$00
               CALL  PRINTSTRING
               DB    +0,+17,$0E,'( ) NO',$00
               CALL  PRINTSTRING
               DB    +24,+15,$0E,'SAVE OPTIONS',$00
               CALL  PRINTSTRING
               DB    +0,+18,$0F,'CHANGE  + INCREASE  - DECREASE',$00
               MOV   AL,'C' AND $3F
               MOV   BL,$09
               MOV   BYTE PTR [CS:CURSORX],+0
               MOV   BYTE PTR [CS:CURSORY],+18
               CALL  PRINTCHAR
               MOV   AL,'+'
               MOV   BYTE PTR [CS:CURSORX],+8
               CALL  PRINTCHAR
               MOV   AL,'-'
               MOV   BYTE PTR [CS:CURSORX],+20
               CALL  PRINTCHAR
               MOV   AX,$FFFF
               MOV   DI,+(18*10-1)*$0120+$0140+12*4
               MOV   CX,+80
               REPZ
               STOSW
@OPT1:         PUSH  DS
               MOV   AX,CS
               MOV   DS,AX
               MOV   BYTE PTR [CS:CURSORY],+7
               MOV   SI,OFFSET EMULCOLORS
               MOV   CH,$00
@OPT11:        MOV   BYTE PTR [CS:CURSORX],+7
               MOV   CL,$03
@OPT10:        LODSB
               MOV   BL,$0E
               CALL  PRINTBYTE
               INC   BYTE PTR [CS:CURSORX]
               DEC   CL
               JNZ   @OPT10
               MOV   BL,CH
               MOV   CL,$07
               MOV   AL,$7F
@OPT12:        CALL  PRINTCHAR
               DEC   CL
               JNZ   @OPT12
               INC   BYTE PTR [CS:CURSORY]
               INC   CH
               CMP   CH,$07
               JB    @OPT11
@OPT33:        POP   DS
               MOV   AX,' *'
               TEST  BYTE PTR [CS:CPUSPEEDMODE],$FF
               JZ    @OPT2
               XCHG  AL,AH
@OPT2:         MOV   BL,$0E
               MOV   BYTE PTR [CS:CURSORX],+1
               MOV   BYTE PTR [CS:CURSORY],+3
               CALL  PRINTCHAR
               DEC   BYTE PTR [CS:CURSORX]
               INC   BYTE PTR [CS:CURSORY]
               MOV   AL,AH
               CALL  PRINTCHAR
               MOV   AX,' *'
               TEST  BYTE PTR [CS:ASMLAYOUT],$FF
               JZ    @OPT4
               XCHG  AL,AH
@OPT4:         MOV   BYTE PTR [CS:CURSORX],+25
               MOV   BYTE PTR [CS:CURSORY],+3
               CALL  PRINTCHAR
               DEC   BYTE PTR [CS:CURSORX]
               INC   BYTE PTR [CS:CURSORY]
               MOV   AL,AH
               CALL  PRINTCHAR
               MOV   AX,' *'
               TEST  BYTE PTR [CS:SOUNDOUTPUT],$FF
               JNZ   @OPT35
               XCHG  AL,AH
@OPT35:        MOV   BYTE PTR [CS:CURSORX],+1
               MOV   BYTE PTR [CS:CURSORY],+16
               CALL  PRINTCHAR
               DEC   BYTE PTR [CS:CURSORX]
               INC   BYTE PTR [CS:CURSORY]
               MOV   AL,AH
               CALL  PRINTCHAR
               MOV   WORD PTR [ES:51924],$FFFF
               MOV   WORD PTR [ES:51926],$FFFF
               CALL  XORPUTOPTCURS
@OPT13:        TEST  BYTE PTR TOETS[CS:$48],$03 {---up---}
               JZ    @OPT14
               CALL  XORPUTOPTCURS
               MOV   BL,BYTE PTR [CS:OPTCURS]
               MOV   BH,$00
               MOV   AL,BYTE PTR @OPTUPTABLE[CS:BX]
               MOV   BYTE PTR [CS:OPTCURS],AL
               CALL  XORPUTOPTCURS
               MOV   BL,$48
               CALL  KEYRELEASE
               JMP   @OPT13
@OPT14:        TEST  BYTE PTR TOETS[CS:$50],$03 {---down---}
               JZ    @OPT15
               CALL  XORPUTOPTCURS
               MOV   BL,BYTE PTR [CS:OPTCURS]
               MOV   BH,$00
               MOV   AL,BYTE PTR @OPTDNTABLE[CS:BX]
               MOV   BYTE PTR [CS:OPTCURS],AL
               CALL  XORPUTOPTCURS
               MOV   BL,$50
               CALL  KEYRELEASE
               JMP   @OPT13
@OPT15:        TEST  BYTE PTR TOETS[CS:$4B],$03 {---left---}
               JZ    @OPT16
               CALL  XORPUTOPTCURS
               MOV   BL,BYTE PTR [CS:OPTCURS]
               MOV   BH,$00
               MOV   AL,BYTE PTR @OPTLFTABLE[CS:BX]
               MOV   BYTE PTR [CS:OPTCURS],AL
               CALL  XORPUTOPTCURS
               MOV   BL,$4B
               CALL  KEYRELEASE
               JMP   @OPT13
@OPT16:        TEST  BYTE PTR TOETS[CS:$4D],$03 {---right---}
               JZ    @OPT17
               CALL  XORPUTOPTCURS
               MOV   BL,BYTE PTR [CS:OPTCURS]
               MOV   BH,$00
               MOV   AL,BYTE PTR @OPTRTTABLE[CS:BX]
               MOV   BYTE PTR [CS:OPTCURS],AL
               CALL  XORPUTOPTCURS
               MOV   BL,$4D
               CALL  KEYRELEASE
               JMP   @OPT13
@OPT17:        MOV   AL,BYTE PTR TOETS[CS:$39] {---space---}
               OR    AL,BYTE PTR TOETS[CS:$2E] {---c---}
               OR    AL,BYTE PTR TOETS[CS:$1C] {---enter---}
               AND   AL,$03
               JZ    @OPT18
               CMP   BYTE PTR [CS:OPTCURS],$04
               JB    @OPT19
               CMP   BYTE PTR [CS:OPTCURS],$19
               JA    @OPT34
               JNZ   @OPT18
               {---save ini-file---}
               CALL  XORPUTOPTCURS
               PUSH  ES
               PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               CALL  WRITEINIFILE
               POP   DS
               POP   ES
@OPT22:        MOV   AL,BYTE PTR TOETS[CS:$39] {---space---}
               OR    AL,BYTE PTR TOETS[CS:$2E] {---c---}
               OR    AL,BYTE PTR TOETS[CS:$1C] {---enter---}
               AND   AL,$03
               JNZ   @OPT22
               JMP   @OPT1
@OPT19:        MOV   AL,BYTE PTR [CS:OPTCURS]
               TEST  AL,$02
               JNZ   @OPT21
               MOV   BYTE PTR [CS:CPUSPEEDMODE],AL
               JMP   @OPT20
@OPT21:        AND   AL,$01
               MOV   BYTE PTR [CS:ASMLAYOUT],AL
@OPT20:        MOV   AL,BYTE PTR TOETS[CS:$39] {---space---}
               OR    AL,BYTE PTR TOETS[CS:$2E] {---c---}
               OR    AL,BYTE PTR TOETS[CS:$1C] {---enter---}
               AND   AL,$03
               JNZ   @OPT20
               CALL  XORPUTOPTCURS
               JMP   @OPT1
@OPT34:        MOV   AL,BYTE PTR [CS:OPTCURS]
               XOR   AL,$01
               AND   AL,$01
               MOV   BYTE PTR [CS:SOUNDOUTPUT],AL
               JMP   @OPT20
@OPT18:        TEST  BYTE PTR TOETS[CS:$0D],$03 {---plus---}
               JZ    @OPT23
               MOV   AL,BYTE PTR [CS:OPTCURS]
               CMP   AL,$04
               JB    @OPT13
               CMP   AL,$18
               JA    @OPT13
               SUB   AL,$04
               MOV   AH,$00
               MOV   BX,AX
               INC   BYTE PTR EMULCOLORS[CS:BX]
               AND   BYTE PTR EMULCOLORS[CS:BX],$3F
               CALL  SETCOLORS
               MOV   DX,$03C8
               MOV   AL,$07
               OUT   DX,AL
               INC   DX
               MOV   AL,$00
               OUT   DX,AL
               OUT   DX,AL
               OUT   DX,AL
               MOV   BL,$0D
               CALL  KEYRELEASE
               CALL  XORPUTOPTCURS
               JMP   @OPT1
@OPT23:        TEST  BYTE PTR TOETS[CS:$0C],$03 {---min---}
               JZ    @OPT24
               MOV   AL,BYTE PTR [CS:OPTCURS]
               CMP   AL,$04
               JB    @OPT13
               CMP   AL,$18
               JA    @OPT13
               SUB   AL,$04
               MOV   AH,$00
               MOV   BX,AX
               DEC   BYTE PTR EMULCOLORS[CS:BX]
               AND   BYTE PTR EMULCOLORS[CS:BX],$3F
               CALL  SETCOLORS
               MOV   DX,$03C8
               MOV   AL,$07
               OUT   DX,AL
               INC   DX
               MOV   AL,$00
               OUT   DX,AL
               OUT   DX,AL
               OUT   DX,AL
               MOV   BL,$0C
               CALL  KEYRELEASE
               CALL  XORPUTOPTCURS
               JMP   @OPT1
@OPT24:        TEST  BYTE PTR TOETS[CS:$42],$03 {---f8---}
               JNZ   @OPT43
               TEST  BYTE PTR TOETS[CS:$43],$03 {---f9---}
               JNZ   @OPT39
               TEST  BYTE PTR TOETS[CS:$57],$03 {---f11---}
               JNZ   @OPT40
               TEST  BYTE PTR TOETS[CS:$38],$03 {---alt---}
               JZ    @OPT25
               TEST  BYTE PTR TOETS[CS:$14],$03 {---t---}
               JZ    @OPT26
@OPT39:        MOV   AL,$01
               JMP   @OPT38
@OPT26:        TEST  BYTE PTR TOETS[CS:$32],$03 {---m---}
               JZ    @OPT44
@OPT40:        MOV   AL,$03
               JMP   @OPT38
@OPT44:        TEST  BYTE PTR TOETS[CS:$20],$03 {---d---}
               JZ    @OPT25
@OPT43:        MOV   AL,$04
               JMP   @OPT38
@OPT25:        TEST  BYTE PTR TOETS[CS:$01],$03 {---escape---}
               JZ    @OPT13
               MOV   AL,$00
@OPT38:        PUSH  AX
               CALL  SETCOLORS
               MOV   DX,$03C8
               MOV   AL,$07
               OUT   DX,AL
               INC   DX
               MOV   AL,$00
               OUT   DX,AL
               OUT   DX,AL
               OUT   DX,AL
               MOV   DI,+10*$0120+$0140+12*4+12*4
               MOV   CX,+7
               MOV   AL,$0B
               CALL  XORPUT
               POP   AX
               RETN
@OPTUPTABLE:   DB    $1B,$00,$19,$02,$01,$01,$01,$04
               DB    $05,$06,$07,$08,$09,$0A,$0B,$0C
               DB    $0D,$0E,$0F,$10,$11,$12,$13,$14
               DB    $15,$03,$16,$1A
@OPTDNTABLE:   DB    $01,$04,$03,$19,$07,$08,$09,$0A
               DB    $0B,$0C,$0D,$0E,$0F,$10,$11,$12
               DB    $13,$14,$15,$16,$17,$18,$1A,$1A
               DB    $1A,$02,$1B,$00
@OPTLFTABLE:   DB    $02,$03,$00,$01,$06,$04,$05,$09
               DB    $07,$08,$0C,$0A,$0B,$0F,$0D,$0E
               DB    $12,$10,$11,$15,$13,$14,$18,$16
               DB    $17,$1A,$19,$19
@OPTRTTABLE:   DB    $02,$03,$00,$01,$05,$06,$04,$08
               DB    $09,$07,$0B,$0C,$0A,$0E,$0F,$0D
               DB    $11,$12,$10,$14,$15,$13,$17,$18
               DB    $16,$1A,$19,$19
END;

{---[monitormode (byte)]----------------------------------------------------}
PROCEDURE MONITORMODE; ASSEMBLER;
ASM;
               DB    $00 {00h=code; 01h=dump}
END;

{---[hexteken (word)]-------------------------------------------------------}
PROCEDURE HEXTEKEN; ASSEMBLER;
ASM;
               DW    $0000 {whether to print #$ or @#}
END;

{---[dmptxt]----------------------------------------------------------------}
PROCEDURE DMPTXT; ASSEMBLER;
ASM;
               DW    $0000,$0000,$0000,$0000
END;

{---[disasptr (word)]-------------------------------------------------------}
PROCEDURE DISASPTR; ASSEMBLER;
ASM;
               DW    $0100
END;

{---[dataptr (word)]--------------------------------------------------------}
PROCEDURE DATAPTR; ASSEMBLER;
ASM;
               DW    $0000
END;

{---[step_ofs (word; holds offset for forward jump into main part)]---------}
PROCEDURE STEP_OFS; ASSEMBLER;
ASM;
               DB    $00
END;

{---[traceorstep (byte)]----------------------------------------------------}
PROCEDURE TRACEORSTEP; ASSEMBLER;
ASM;
               DB    $00 {00h=trace;01h=step}
END;

{---[trace_ofs (word; holds offset for forward jump into main part)]--------}
PROCEDURE TRACE_OFS; ASSEMBLER;
ASM;
               DB    $00
END;

{---[untilcursor_ofs (word; holds offset for forward jump into main part)]--}
PROCEDURE UNTILCURSOR_OFS; ASSEMBLER;
ASM;
               DB    $00
END;

{---[breakpoint_ofs (word; holds offset for forward jump into main part)]---}
PROCEDURE BREAKPOINT_OFS; ASSEMBLER;
ASM;
               DB    $00
END;

{---[clreol (works only until column +30)]----------------------------------}
PROCEDURE CLREOL; ASSEMBLER;
ASM;
               PUSH  WORD PTR [CS:CURSORX]
@CLREOL2:      CMP   BYTE PTR [CS:CURSORX],+30
               JA    @CLREOL1
               MOV   AL,' '
               CALL  PRINTCHAR
               JMP   @CLREOL2
@CLREOL1:      POP   WORD PTR [CS:CURSORX]
END;

{---[disas; DS:SI=startofs; BX=endofs]--------------------------------------}
PROCEDURE DISAS; ASSEMBLER;
ASM;
               PUSH  BX
               MOV   AL,BYTE PTR [SI]
               MOV   BL,AL
               MOV   BH,$00
               SHL   BX,1
               MOV   CH,BYTE PTR OPCODES[CS:BX    ]
               MOV   CL,BYTE PTR OPCODES[CS:BX+$01]
               MOV   BL,$0B
               MOV   AL,'.'
               CALL  PRINTCHAR
               MOV   AX,SI
               CALL  PRINTWORD
               MOV   AL,' '
               CALL  PRINTCHAR
               MOV   AL,BYTE PTR [SI]
               CALL  PRINTBYTE
               MOV   AL,' '
               CALL  PRINTCHAR
               CMP   CL,+1
               JZ    @DIS3
               CMP   CL,+9
               JZ    @DIS3
@DIS2:         INC   SI
               MOV   AL,BYTE PTR [SI]
               DEC   SI
               CALL  PRINTBYTE
               JMP   @DIS4
@DIS3:         MOV   AL,' '
               CALL  PRINTCHAR
               CALL  PRINTCHAR
@DIS4:         MOV   AL,' '
               CALL  PRINTCHAR
               CMP   CL,+13
               JZ    @DIS5
               CMP   CL,+15
               JZ    @DIS5
               CMP   CL,+6
               JB    @DIS6
               CMP   CL,+8
               JA    @DIS6
@DIS5:         MOV   AL,BYTE PTR [SI+$02]
               CALL  PRINTBYTE
               JMP   @DIS7
@DIS6:         MOV   AL,' '
               CALL  PRINTCHAR
               CALL  PRINTCHAR
@DIS7:         MOV   AL,' '
               CALL  PRINTCHAR
               MOV   AL,CH
               MOV   AH,$00
               PUSH  SI
               MOV   SI,AX
               SHL   AX,1
               ADD   SI,AX
               MOV   AL,BYTE PTR MNEMONICS[CS:SI]
               AND   AL,$3F
               CALL  PRINTCHAR
               INC   SI
               MOV   AL,BYTE PTR MNEMONICS[CS:SI]
               AND   AL,$3F
               CALL  PRINTCHAR
               INC   SI
               MOV   AL,BYTE PTR MNEMONICS[CS:SI]
               AND   AL,$3F
               CALL  PRINTCHAR
               POP   SI
               MOV   AL,' '
               CALL  PRINTCHAR
               CMP   CL,+11
               JB    @DIS8
               MOV   AL,'('
               CALL  PRINTCHAR
@DIS8:         CMP   CL,+2
               JNZ   @DIS9
               MOV   AL,BYTE PTR [CS:HEXTEKEN+$01]
               CALL  PRINTCHAR
@DIS9:         CMP   CL,+1
               JB    @DIS10
               JA    @DIS36
               MOV   AL,'A' AND $3F
               JMP   @DIS37
@DIS36:        CMP   CL,+9
               JZ    @DIS10
               MOV   AL,BYTE PTR [CS:HEXTEKEN]
@DIS37:        CALL  PRINTCHAR
@DIS10:        CMP   CL,+10
               JNZ   @DIS11
               MOV   AL,BYTE PTR [SI+$01]
               TEST  AL,$80
               JZ    @DIS12
               NEG   AL
               MOV   AH,$00
               PUSH  BX
               MOV   BX,AX
               MOV   AX,SI
               ADD   AX,+$02
               SUB   AX,BX
               POP   BX
               JMP   @DIS13
@DIS12:        MOV   AH,$00
               ADD   AX,SI
               ADD   AX,+$02
               JMP   @DIS13
@DIS11:        CMP   CL,+13
               JZ    @DIS14
               CMP   CL,+15
               JZ    @DIS14
               CMP   CL,+6
               JB    @DIS15
               CMP   CL,+8
               JA    @DIS15
@DIS14:        MOV   AX,WORD PTR [SI+$01]
               JMP   @DIS13
@DIS15:        MOV   AL,BYTE PTR [SI+$01]
               MOV   AH,$00
@DIS13:        CMP   CL,+1
               JBE   @DIS16
               CMP   CL,+9
               JZ    @DIS16
               CMP   CL,+10
               JZ    @DIS17
               CMP   CL,+13
               JZ    @DIS17
               CMP   CL,+15
               JZ    @DIS17
               CMP   CL,+6
               JB    @DIS18
               CMP   CL,+9
               JBE   @DIS17
@DIS18:        CALL  PRINTBYTE
               JMP   @DIS16
@DIS17:        CALL  PRINTWORD
@DIS16:        CMP   CL,+4
               JZ    @DIS19
               CMP   CL,+7
               JZ    @DIS19
               CMP   CL,+11
               JZ    @DIS19
               CMP   CL,+15
               JNZ   @DIS20
@DIS19:        MOV   AL,','
               CALL  PRINTCHAR
               MOV   AL,'X' AND $3F
               CALL  PRINTCHAR
@DIS20:        CMP   CL,+5
               JZ    @DIS21
               CMP   CL,+8
               JNZ   @DIS22
@DIS21:        MOV   AL,','
               CALL  PRINTCHAR
               MOV   AL,'Y' AND $3F
               CALL  PRINTCHAR
@DIS22:        CMP   CL,+11
               JZ    @DIS23
               CMP   CL,+13
               JB    @DIS24
@DIS23:        MOV   AL,')'
               CALL  PRINTCHAR
@DIS24:        CMP   CL,+12
               JNZ   @DIS25
               MOV   AL,')'
               CALL  PRINTCHAR
               MOV   AL,','
               CALL  PRINTCHAR
               MOV   AL,'Y' AND $3F
               CALL  PRINTCHAR
@DIS25:        CALL  CLREOL
               CALL  NEXTLINE
               CMP   CL,+1
               JZ    @DIS27
               CMP   CL,+9
               JNZ   @DIS28
@DIS27:        INC   SI
               JZ    @DIS35
               JMP   @DIS32
@DIS28:        CMP   CL,+6
               JB    @DIS29
               CMP   CL,+9
               JBE   @DIS30
               CMP   CL,+13
               JNZ   @DIS29
@DIS30:        INC   SI
               JZ    @DIS35
@DIS29:        ADD   SI,$0002
               JC    @DIS35
@DIS32:        POP   BX
               CMP   SI,BX
               JA    @DIS33
               JMP   DISAS
@DIS33:        RETN
@DIS35:        POP   BX
END;

{---[dump; DS:SI=startofs; BX=endofs (moet veelvoud van 08h verder zijn)]---}
PROCEDURE DUMP; ASSEMBLER;
ASM;
               INC   BX
               MOV   CX,BX
@DUMP5:        MOV   AX,'  '
               MOV   WORD PTR DMPTXT[CS:$0000],AX
               MOV   WORD PTR DMPTXT[CS:$0002],AX
               MOV   WORD PTR DMPTXT[CS:$0004],AX
               MOV   WORD PTR DMPTXT[CS:$0006],AX
               MOV   BL,$0B
               MOV   AL,':'
               CALL  PRINTCHAR
               MOV   AX,SI
               CALL  PRINTWORD
               MOV   AL,' '
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               SUB   DI,DI
@DUMP3:        LODSB
               MOV   AH,AL
               AND   AL,$7F
               CMP   AL,'A'
               JB    @DUMP12
               CMP   AL,'Z'
               JA    @DUMP12
               AND   AL,$3F
               JMP   @DUMP1
@DUMP12:       CMP   AL,$40
               JAE   @DUMP8
               CMP   AL,$20
               JAE   @DUMP1
@DUMP8:        MOV   AL,'.'
@DUMP1:        OR    AL,$80
               MOV   BYTE PTR DMPTXT[CS:DI],AL
               INC   DI
               MOV   AL,AH
               CALL  PRINTBYTE
               MOV   AL,' '
               CALL  PRINTCHAR
               CMP   DI,$0008
               JB    @DUMP3
@DUMP2:        CMP   BYTE PTR [CS:CURSORX],$20
               JAE   @DUMP4
               MOV   AL,' '
               CALL  PRINTCHAR
               JMP   @DUMP2
@DUMP4:        SUB   DI,DI
@DUMP6:        MOV   AL,BYTE PTR DMPTXT[CS:DI]
               CALL  PRINTCHAR
               INC   DI
               CMP   DI,$0008
               JB    @DUMP6
@DUMP10:       CMP   SI,CX
               JNZ   @DUMP5
END;

{---[showreg]---------------------------------------------------------------}
PROCEDURE SHOWREG; ASSEMBLER;
ASM;
               MOV   BYTE PTR [CS:CURSORX],+32
               MOV   BYTE PTR [CS:CURSORY],+2
               MOV   BL,$0E
               MOV   AL,'P' AND $3F
               CALL  PRINTCHAR
               MOV   AL,'C' AND $3F
               CALL  PRINTCHAR
               MOV   BL,$09
               MOV   AL,'='
               CALL  PRINTCHAR
               MOV   BL,$0E
               MOV   AL,BYTE PTR [CS:HEXTEKEN]
               CALL  PRINTCHAR
               MOV   AX,WORD PTR [CS:PROGRAMCNT]
               CALL  PRINTWORD
               MOV   BYTE PTR [CS:CURSORX],+32
               MOV   BYTE PTR [CS:CURSORY],+3
               MOV   BL,$0E
               MOV   AL,'A' AND $3F
               CALL  PRINTCHAR
               MOV   AL,' ' AND $3F
               CALL  PRINTCHAR
               MOV   BL,$09
               MOV   AL,'='
               CALL  PRINTCHAR
               MOV   BL,$0E
               MOV   AL,BYTE PTR [CS:HEXTEKEN]
               CALL  PRINTCHAR
               MOV   AH,BYTE PTR [CS:ACCU_B]
               MOV   AL,BYTE PTR [CS:ACCUMULATOR]
               CALL  PRINTWORD
               MOV   BYTE PTR [CS:CURSORX],+32
               MOV   BYTE PTR [CS:CURSORY],+4
               MOV   BL,$0E
               MOV   AL,'X' AND $3F
               CALL  PRINTCHAR
               MOV   AL,' ' AND $3F
               CALL  PRINTCHAR
               MOV   BL,$09
               MOV   AL,'='
               CALL  PRINTCHAR
               MOV   BL,$0E
               MOV   AL,BYTE PTR [CS:HEXTEKEN]
               CALL  PRINTCHAR
               MOV   AL,BYTE PTR [CS:XREGISTER]
               CALL  PRINTBYTE
               MOV   BYTE PTR [CS:CURSORX],+32
               MOV   BYTE PTR [CS:CURSORY],+5
               MOV   BL,$0E
               MOV   AL,'Y' AND $3F
               CALL  PRINTCHAR
               MOV   AL,' ' AND $3F
               CALL  PRINTCHAR
               MOV   BL,$09
               MOV   AL,'='
               CALL  PRINTCHAR
               MOV   BL,$0E
               MOV   AL,BYTE PTR [CS:HEXTEKEN]
               CALL  PRINTCHAR
               MOV   AL,BYTE PTR [CS:YREGISTER]
               CALL  PRINTBYTE
               MOV   BYTE PTR [CS:CURSORX],+32
               MOV   BYTE PTR [CS:CURSORY],+6
               MOV   BL,$0E
               MOV   AL,'S' AND $3F
               CALL  PRINTCHAR
               MOV   AL,'P' AND $3F
               CALL  PRINTCHAR
               MOV   BL,$09
               MOV   AL,'='
               CALL  PRINTCHAR
               MOV   BL,$0E
               MOV   AL,BYTE PTR [CS:HEXTEKEN]
               CALL  PRINTCHAR
               MOV   AX,WORD PTR [CS:STACKPOINTER]
               CALL  PRINTBYTE
               CALL  PRINTSTRING
               DB    +32,+7,$0E,'NV-BDIZC',$00
               MOV   BYTE PTR [CS:CURSORX],+32
               MOV   BYTE PTR [CS:CURSORY],+8
               MOV   CL,$80
@SHOWREG2:     MOV   AL,'0'
               TEST  BYTE PTR [CS:FLAGREGISTER],CL
               JZ    @SHOWREG1
               MOV   AL,'1'
@SHOWREG1:     CALL  PRINTCHAR
               SHR   CL,1
               JNC   @SHOWREG2
END;

{---[monitor (desktop)]-----------------------------------------------------}
PROCEDURE MONITOR; ASSEMBLER;
ASM;
               MOV   BL,BYTE PTR [CS:ASMLAYOUT]
               MOV   BH,$00
               SHL   BX,1
               MOV   AX,WORD PTR @WHICHHEXSIGN[BX]
               MOV   WORD PTR [CS:HEXTEKEN],AX
               MOV   DI,+20*$0120+$0140
               MOV   CX,+168*$0120/4
@MON48:        MOV   AX,$00FF
               STOSW
               MOV   AX,$FFFF
               STOSW
               LOOP  @MON48
               MOV   DI,+10*$0120+$0140+12*4+21*4
               MOV   CX,+7
               MOV   AL,$0B
               CALL  XORPUT
               CALL  PRINTSTRING
               DB    +0,+18,$0F,'TRACE STEP HERE BRKPNT GOTO WHERE MODE',$00
               MOV   AL,'T' AND $3F
               MOV   BL,$09
               MOV   BYTE PTR [CS:CURSORX],+0
               MOV   BYTE PTR [CS:CURSORY],+18
               CALL  PRINTCHAR
               MOV   AL,'S' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+6
               CALL  PRINTCHAR
               MOV   AL,'H' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+11
               CALL  PRINTCHAR
               MOV   AL,'B' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+16
               CALL  PRINTCHAR
               MOV   AL,'G' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+23
               CALL  PRINTCHAR
               MOV   AL,'W' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+28
               CALL  PRINTCHAR
               MOV   AL,'M' AND $3F
               MOV   BYTE PTR [CS:CURSORX],+34
               CALL  PRINTCHAR
@MON5:         SUB   CX,CX
@MON52:        MOV   SI,CX
               SHL   SI,1
               MOV   AX,WORD PTR @BRKPNTCOORD[CS:SI]
               MOV   BYTE PTR [CS:CURSORX],AL
               MOV   BYTE PTR [CS:CURSORY],AH
               MOV   AL,$01
               SHL   AL,CL
               TEST  BYTE PTR [CS:BRKPNTON],AL
               JNZ   @MON53
               MOV   AL,' '
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               CALL  PRINTCHAR
               JMP   @MON54
@MON53:        MOV   AX,WORD PTR BRKPNTS[CS:SI]
               MOV   BL,$09
               CMP   AX,WORD PTR [CS:DISASPTR]
               JNZ   @MON55
               MOV   BL,$0F
@MON55:        CALL  PRINTWORD
@MON54:        INC   CL
               CMP   CL,$04
               JNZ   @MON52
               TEST  BYTE PTR [CS:MONITORMODE],$FF
               JZ    @MON33
               CALL  PRINTSTRING
               DB    +36,+12,$0C,'DUMP',$00
               JMP   @MON57
@MON33:        CALL  PRINTSTRING
               DB    +36,+12,$0C,'CODE',$00
@MON57:        MOV   DS,WORD PTR [CS:ATOMSEG]
               MOV   BYTE PTR [CS:CURSORX],+0
               MOV   BYTE PTR [CS:CURSORY],+2
               MOV   SI,WORD PTR [CS:DISASPTR]
@MON3:         MOV   BX,SI
               CALL  DISAS
               CMP   BYTE PTR [CS:CURSORY],+13
               JB    @MON3
               INC   BYTE PTR [CS:CURSORY]
               MOV   SI,WORD PTR [CS:DATAPTR]
@MON2:         MOV   BX,SI
               ADD   BX,+$07
               CALL  DUMP
               CMP   BYTE PTR [CS:CURSORY],+18
               JB    @MON2
               MOV   AX,$FFFF
               MOV   DI,+(18*10-1)*$0120+$0140+12*4
               MOV   CX,+80
               REPZ
               STOSW
               CALL  SHOWREG
@MON26:        TEST  BYTE PTR TOETS[CS:$32],$03 {---m---}
               JNZ   @MON26
@MON6:         TEST  BYTE PTR TOETS[CS:$1F],$03 {---s---}
               JZ    @MON1
               OR    BYTE PTR [CS:BRKPNTON],$80
               CALL  WORD PTR [CS:STEP_OFS]
               AND   BYTE PTR [CS:BRKPNTON],$7F
               MOV   BL,$1F {---s---}
               CALL  KEYRELEASE
               MOV   AX,WORD PTR [CS:PROGRAMCNT]
               MOV   WORD PTR [CS:DISASPTR],AX
               TEST  BYTE PTR [CS:TRACEORSTEP],$FF
               JZ    @MON5
               CALL  UPPERLINES
               JMP   MONITOR
@MON1:         TEST  BYTE PTR TOETS[CS:$14],$03 {---t---}
               JZ    @MON7
               TEST  BYTE PTR TOETS[CS:$38],$03 {---alt---}
               JNZ   @MON7
               OR    BYTE PTR [CS:BRKPNTON],$80
               CALL  WORD PTR [CS:TRACE_OFS]
               AND   BYTE PTR [CS:BRKPNTON],$7F
               MOV   BL,$14 {---t---}
               CALL  KEYRELEASE
               MOV   AX,WORD PTR [CS:PROGRAMCNT]
               MOV   WORD PTR [CS:DISASPTR],AX
               JMP   @MON5
@MON7:         TEST  BYTE PTR TOETS[CS:$48],$03 {---up---}
               JZ    @MON9
               TEST  BYTE PTR [CS:MONITORMODE],$FF
               JZ    @MON34
               SUB   WORD PTR [CS:DATAPTR],+$08
               MOV   BL,$48 {---up---}
               CALL  KEYRELEASE
               JMP   @MON5
@MON34:        MOV   SI,WORD PTR [CS:DISASPTR]
               SUB   SI,+$18
@MON15:        MOV   CX,SI
               MOV   BL,BYTE PTR [SI]
               MOV   BH,$00
               SHL   BX,1
               MOV   BL,BYTE PTR OPCODES[CS:BX+$01]
               DEC   BL
               MOV   BH,$00
               MOV   AL,BYTE PTR @SI_ERBIJ[BX]
               MOV   AH,$00
               ADD   SI,AX
               CMP   SI,WORD PTR [CS:DISASPTR]
               JB    @MON15
               JA    @MON18
               MOV   SI,CX
               JMP   @MON11
@MON18:        MOV   SI,WORD PTR [CS:DISASPTR]
               SUB   SI,+$03
               MOV   AL,$03
@MON12:        MOV   BL,BYTE PTR [SI]
               MOV   BH,$00
               SHL   BX,1
               MOV   BL,BYTE PTR OPCODES[CS:BX+$01]
               DEC   BL
               MOV   BH,$00
               CMP   BYTE PTR @SI_ERBIJ[BX],AL
               JZ    @MON11
               INC   SI
               DEC   AL
               CMP   AL,$01
               JA    @MON12
@MON11:        MOV   WORD PTR [CS:DISASPTR],SI
               MOV   BL,$48 {---up---}
               CALL  KEYRELEASE
               JMP   @MON5
@MON9:         TEST  BYTE PTR TOETS[CS:$50],$03 {---down---}
               JZ    @MON10
               TEST  BYTE PTR [CS:MONITORMODE],$FF
               JZ    @MON35
               ADD   WORD PTR [CS:DATAPTR],+$08
               MOV   BL,$50 {---down---}
               CALL  KEYRELEASE
               JMP   @MON5
@MON35:        MOV   SI,WORD PTR [CS:DISASPTR]
               MOV   BL,BYTE PTR [SI]
               MOV   BH,$00
               SHL   BX,1
               MOV   BL,BYTE PTR OPCODES[CS:BX+$01]
               DEC   BL
               MOV   BH,$00
               MOV   AL,BYTE PTR @SI_ERBIJ[BX]
               MOV   AH,$00
               ADD   WORD PTR [CS:DISASPTR],AX
               MOV   BL,$50 {---down---}
               CALL  KEYRELEASE
               JMP   @MON5
@MON10:        TEST  BYTE PTR TOETS[CS:$4B],$03 {---left---}
               JZ    @MON21
               TEST  BYTE PTR [CS:MONITORMODE],$FF
               JZ    @MON41
               DEC   WORD PTR [CS:DATAPTR]
               JMP   @MON42
@MON41:        DEC   WORD PTR [CS:DISASPTR]
@MON42:        MOV   BL,$4B {---left---}
               CALL  KEYRELEASE
               JMP   @MON5
@MON21:        TEST  BYTE PTR TOETS[CS:$4D],$03 {---right---}
               JZ    @MON20
               TEST  BYTE PTR [CS:MONITORMODE],$FF
               JZ    @MON43
               INC   WORD PTR [CS:DATAPTR]
               JMP   @MON44
@MON43:        INC   WORD PTR [CS:DISASPTR]
@MON44:        MOV   BL,$4D {---right---}
               CALL  KEYRELEASE
               JMP   @MON5
@MON20:        TEST  BYTE PTR TOETS[CS:$49],$03 {---page up---}
               JZ    @MON22
               TEST  BYTE PTR [CS:MONITORMODE],$FF
               JZ    @MON36
               SUB   WORD PTR [CS:DATAPTR],+$20
               JMP   @MON37
@MON36:        SUB   WORD PTR [CS:DISASPTR],+$10
@MON37:        MOV   BL,$49 {---page up---}
               CALL  KEYRELEASE
               JMP   @MON5
@MON22:        TEST  BYTE PTR TOETS[CS:$51],$03 {---page down---}
               JZ    @MON28
               TEST  BYTE PTR [CS:MONITORMODE],$FF
               JZ    @MON38
               ADD   WORD PTR [CS:DATAPTR],+$20
               JMP   @MON39
@MON38:        ADD   WORD PTR [CS:DISASPTR],+$10
@MON39:        MOV   BL,$51 {---page down---}
               CALL  KEYRELEASE
               JMP   @MON5
@MON28:        TEST  BYTE PTR TOETS[CS:$22],$03 {---g---}
               JZ    @MON27
               MOV   BYTE PTR [CS:CURSORX],+9
               MOV   BYTE PTR [CS:CURSORY],+7
               MOV   BL,$0C
               MOV   AL,01000101b
               CALL  PRINTCHAR
               MOV   CX,+20
               MOV   AL,01001100b
@MON29:        CALL  PRINTCHAR
               LOOP  @MON29
               MOV   AL,01001010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+9
               MOV   BYTE PTR [CS:CURSORY],+8
               MOV   AL,01010101b
               CALL  PRINTCHAR
               CALL  PRINTSTRING
               DB    +10,+8,$0E,' GOTO ADDRESS:      ',$00
               MOV   BL,$0C
               MOV   AL,01101010b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+9
               MOV   BYTE PTR [CS:CURSORY],+9
               MOV   AL,01010100b
               CALL  PRINTCHAR
               MOV   CX,+20
               MOV   AL,01001100b
@MON30:        CALL  PRINTCHAR
               LOOP  @MON30
               MOV   AL,01101000b
               CALL  PRINTCHAR
               MOV   BYTE PTR [CS:CURSORX],+25
               MOV   BYTE PTR [CS:CURSORY],+8
               CALL  INPUTWORD
               JC    @MON5
               TEST  BYTE PTR [CS:MONITORMODE],$FF
               JZ    @MON40
               MOV   WORD PTR [CS:DATAPTR],AX
               JMP   @MON5
@MON40:        MOV   WORD PTR [CS:DISASPTR],AX
               JMP   @MON5
@MON27:        TEST  BYTE PTR TOETS[CS:$23],$03 {---h---}
               JZ    @MON56
               OR    BYTE PTR [CS:BRKPNTON],$80
               CALL  WORD PTR [CS:UNTILCURSOR_OFS]
               AND   BYTE PTR [CS:BRKPNTON],$7F
               MOV   AX,WORD PTR [CS:PROGRAMCNT]
               MOV   WORD PTR [CS:DISASPTR],AX
               CALL  UPPERLINES
               JMP   MONITOR
@MON56:        TEST  BYTE PTR TOETS[CS:$30],$03 {---b---}
               JZ    @MON31
               CALL  WORD PTR [CS:BREAKPOINT_OFS]
               CALL  UPPERLINES
               JMP   MONITOR
@MON31:        TEST  BYTE PTR TOETS[CS:$32],$03 {---m---}
               JZ    @MON32
               TEST  BYTE PTR TOETS[CS:$38],$03 {---alt---}
               JNZ   @MON32
               XOR   BYTE PTR [CS:MONITORMODE],$01
               MOV   BL,$32 {---m---}
               CALL  KEYRELEASE
               JMP   @MON5
@MON32:        TEST  BYTE PTR TOETS[CS:$11],$03 {---w---}
               JZ    @MON49
               MOV   AX,WORD PTR [CS:PROGRAMCNT]
               MOV   WORD PTR [CS:DISASPTR],AX
               MOV   BL,$11 {---w---}
               CALL  KEYRELEASE
               JMP   @MON5
@MON49:        TEST  BYTE PTR TOETS[CS:$42],$03 {---f8---}
               JNZ   @MON58
               TEST  BYTE PTR TOETS[CS:$43],$03 {---f9---}
               JNZ   @MON50
               TEST  BYTE PTR TOETS[CS:$44],$03 {---f10---}
               JNZ   @MON51
               TEST  BYTE PTR TOETS[CS:$38],$03 {---alt---}
               JZ    @MON25
@MON23:        TEST  BYTE PTR TOETS[CS:$14],$03 {---t---}
               JZ    @MON24
@MON50:        MOV   DI,+10*$0120+$0140+12*4+21*4
               MOV   CX,+7
               MOV   AL,$0B
               CALL  XORPUT
               MOV   AL,$01
               RETN
@MON24:        TEST  BYTE PTR TOETS[CS:$18],$03 {---o---}
               JZ    @MON59
@MON51:        MOV   DI,+10*$0120+$0140+12*4+21*4
               MOV   CX,+7
               MOV   AL,$0B
               CALL  XORPUT
               MOV   AL,$02
               RETN
@MON59:        TEST  BYTE PTR TOETS[CS:$20],$03 {---d---}
               JZ    @MON25
@MON58:        MOV   DI,+10*$0120+$0140+12*4+21*4
               MOV   CX,+7
               MOV   AL,$0B
               CALL  XORPUT
               MOV   AL,$04
               RETN
@MON25:        TEST  BYTE PTR TOETS[CS:$01],$03 {---escape---}
               JZ    @MON6
               MOV   DI,+10*$0120+$0140+12*4+21*4
               MOV   CX,+7
               MOV   AL,$0B
               CALL  XORPUT
               MOV   AL,$00
               RETN
@SI_ERBIJ:     DB    1,2,2,2,2,3,3,3,1,2,2,2,3,2,3
@WHICHHEXSIGN: DB    '#','@' AND $3F,'$#'
@BRKPNTCOORD:  DB    +36,+10
               DB    +31,+10
               DB    +36,+11
               DB    +31,+11
END;

{===[program]===============================================================}
VAR I:BYTE;
BEGIN
SETUPSPEEDLOOP;
WRITELN ('Acorn Atom Emulator v1.33 (c) by Wouter Ras.');
INITIALIZE;
WRITELN ('Seaching directory for tape and disk images.');
READDIRECTORY;
IF AANTALTAPEIMAGES > 0 THEN
BEGIN
  TAPEIMAGENAME := TAPEIMAGES[0];
  READFILESINTAPEIMAGE;
END;
READINIFILE;
IF MEM[CSEG:OFS(LEENDERTSROM)] <> 0 THEN
  WRITELN ('Installing co-processor support (c) Roland Leurs/Leendert Bijnagte.');
COPYWRITEPROT;
TIMER;
FOR I := 0 TO 3 DO
BEGIN
  IF DISKETTENAMES[I] <> '' THEN
    OPEN_DISK_IMAGE (I,(WRITEPROTECT[I AND 1] SHR ((I AND $02) SHL 1))<>0);
END;
WACHTEVENTJES;
ASM;
{---[main]------------------------------------------------------------------}
               MOV   WORD PTR [CS:RESETANDLOAD_OFS],OFFSET @RESETANDLOAD
               MOV   WORD PTR [CS:STEP_OFS],OFFSET @STEP
               MOV   WORD PTR [CS:TRACE_OFS],OFFSET @TRACE
               MOV   WORD PTR [CS:UNTILCURSOR_OFS],OFFSET @UNTILCURSOR
               MOV   WORD PTR [CS:BREAKPOINT_OFS],OFFSET @BREAKPOINT
               MOV   AX,WORD PTR IOPORT
               OR    AX,AX
               JZ    @MAIN9
               MOV   AL,$01
@MAIN9:        MOV   BYTE PTR @SBAVAIL,AL
               {---make widertable---}
               SUB   DI,DI
               MOV   BL,$00
@INIT11:       MOV   BH,BL
               SUB   AX,AX
               MOV   CX,$0008
@INIT10:       SHL   BH,1
               JNC   @INIT8
               RCL   AX,1
               STC
               RCL   AX,1
               JMP   @INIT9
@INIT8:        SHL   AX,2
@INIT9:        LOOP  @INIT10
               XCHG  AL,AH
               MOV   WORD PTR WIDERTABLE[CS:DI],AX
               ADD   DI,+$02
               INC   BL
               JNZ   @INIT11
               {---make wider1atable---}
               SUB   DI,DI
               MOV   BL,$00
@INIT7:        MOV   BH,BL
               SUB   AX,AX
               MOV   CX,$0004
@INIT6:        MOV   DL,$02
@INIT1:        PUSH  BX
               SHL   BH,1
               JNC   @INIT4
               RCL   AX,1
               JMP   @INIT5
@INIT4:        SHL   AX,1
@INIT5:        SHL   BX,1
               JNC   @INIT2
               RCL   AX,1
               JMP   @INIT3
@INIT2:        SHL   AX,1
@INIT3:        POP   BX
               DEC   DL
               JNZ   @INIT1
               SHL   BH,2
               LOOP  @INIT6
               XCHG  AL,AH
               MOV   WORD PTR WIDER1aTABLE[CS:DI],AX
               ADD   DI,+$02
               INC   BL
               JNZ   @INIT7
               CLD
               MOV   AX,WORD PTR ATOMMEMSEG
               MOV   WORD PTR [CS:ATOMSEG],AX
               MOV   BYTE PTR [CS:GRAPHMODE],$00
               PUSH  DS
               MOV   AX,DS
               MOV   ES,AX
               MOV   AX,CS
               MOV   DS,AX
               {---characters---}
               MOV   SI,OFFSET CHARACTERS
               MOV   DI,OFFSET CHARDATA
               MOV   BL,$40
@MAIN1:        MOV   AL,$00
               STOSB
               STOSB
               STOSB
               MOV   CX,$0007
@MAIN3:        LODSB
               ROL   AL,1
               STOSB
               LOOP  @MAIN3
               MOV   AL,$00
               STOSB
               STOSB
               ADD   DI,+$04
               DEC   BL
               JNZ   @MAIN1
               {---inverted characters---}
               MOV   SI,OFFSET CHARACTERS
               MOV   DI,OFFSET CHARDATA+$0800
               MOV   BL,$40
@MAIN2:        MOV   AL,$FF
               STOSB
               STOSB
               STOSB
               MOV   CX,$0007
@MAIN4:        LODSB
               ROL   AL,1
               NOT   AL
               STOSB
               LOOP  @MAIN4
               MOV   AL,$FF
               STOSB
               STOSB
               ADD   DI,+$04
               DEC   BL
               JNZ   @MAIN2
               {---white/grey graphics symbols---}
               MOV   DI,OFFSET CHARDATA+$0400
               MOV   BL,$40
@MAIN5:        MOV   BH,00100000b
@MAIN8:        MOV   AL,$00
               TEST  BL,BH
               JZ    @MAIN6
               OR    AL,$F0
@MAIN6:        SHR   BH,1
               TEST  BL,BH
               JZ    @MAIN7
               OR    AL,$0F
@MAIN7:        STOSB
               STOSB
               STOSB
               STOSB
               SHR   BH,1
               JNC   @MAIN8
               ADD   DI,+$04
               INC   BL
               CMP   BL,$80
               JB    @MAIN5
               POP   DS
               CALL  INITATOMGRAPH
               MOV   AX,$A000
               MOV   ES,AX
               CALL  @SETINT
               MOV   DS,WORD PTR ATOMMEMSEG
               MOV   BYTE PTR [$B001],$FF
               MOV   BYTE PTR [$B002],$40
               MOV   WORD PTR [INSTRCYCLES],$0000
               MOV   WORD PTR [PCCYCLES],$0000
               MOV   WORD PTR [WACHTSCHULD],$0000
               CALL  @VOLUMEON
               CALL  SETBORDERCOL
               CALL  SETINTENSCOL
               PUSH  DS
               PUSH  ES
               PUSHA
               PUSHF
               MOV   WORD PTR @PCSP,SP
               JMP   @BREAKKEY
@ENDOFEMUL:    MOV   SP,WORD PTR @PCSP
               POPF
               POPA
               POP   ES
               POP   DS
               CALL  @VOLUMEOFF
               CALL  @CLRINT
               MOV   AX,$0003
               INT   $10
               MOV   AX,CS
               MOV   DS,AX
               MOV   DX,OFFSET @BYEBYETXT
               MOV   AH,$09
               INT   $21
               MOV   DS,WORD PTR [CS:DATASEG]
               JMP   @ENDOFPRG
@BYEBYETXT:    DB    'Acorn Atom Emulator v1.33 (c) Wouter Ras, Delft, '
               DB    'Oct 1997 - May 1999.',$0D,$0A,$0A,'Bye bye!'
               DB    $0D,$0A,$0A,'$'

{---[00h: brk implied]------------------------------------------------------}
@OPCODE00:     MOV   WORD PTR [INSTRCYCLES],$1507
               MOV   AX,SI
               INC   AX
               AND   BP,$00FF
               MOV   BYTE PTR [DS:BP+STACKBASE],AH
               DEC   BP
               AND   BP,$00FF
               MOV   BYTE PTR [DS:BP+STACKBASE],AL
               DEC   BP
               AND   BP,$00FF
               MOV   AL,BH
               OR    AL,00010000b {set break flag}
               MOV   BYTE PTR [DS:BP+STACKBASE],AL
               DEC   BP
               OR    BH,00000100b {set interrupt flag}
               MOV   SI,WORD PTR [BRK_VECTOR]
               JMP   @NEXTOPC

{---[01h: ora (indirect,x)]-------------------------------------------------}
@OPCODE01:     MOV   WORD PTR [INSTRCYCLES],$1406+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   DI,WORD PTR [DI] {get address from atom memory}
               OR    BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[02h: cop implied]------------------------------------------------------}
@OPCODE02:     TEST  BYTE PTR [CS:LEENDERTSROM],$FF
               JNZ   @OPC02_1
               MOV   WORD PTR [INSTRCYCLES],$0B03
               INC   SI
               JMP   @NEXTOPC
@OPC02_1:      MOV   WORD PTR [INSTRCYCLES],$4007
               PUSH  DS
               PUSH  ES
               PUSHA
               MOV   AL,BL
               MOV   BL,CL
               MOV   BH,DL
               PUSH  DS
               POP   ES
               DB    $2E,$FF,$1E
               DW    OFFSET FPPC_ADDR
               TEST  AL,$01
               JZ    @OPC02_2
               {---invalid operation: generate error 123---}
               POPA
               POP   ES
               POP   DS
               MOV   SI,+122
               JMP   @OPCODE00
@OPC02_2:      TEST  AL,$04
               JZ    @OPC02_3
               {---division by zero error; generate error 169---}
               POPA
               POP   ES
               POP   DS
               MOV   SI,+168
               JMP   @OPCODE00
@OPC02_3:      TEST  AL,$40
               JZ    @OPC02_4
               {---power of neg.number with non-int exp: error 191---}
               POPA
               POP   ES
               POP   DS
               MOV   SI,+190
               JMP   @OPCODE00
@OPC02_4:      POPA
               POP   ES
               POP   DS
               JMP   @NEXTOPC

{---[04h: tsb zero page]----------------------------------------------------}
@OPCODE04:     MOV   WORD PTR [INSTRCYCLES],$1205+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               TEST  BL,BYTE PTR [DI]
               LAHF
               OR    BYTE PTR [DI],BL
               AND   BH,11111101b
               AND   AH,01000000b
               SHR   AH,5
               OR    BH,AH {zero flag}
               JMP   @NEXTOPC

{---[05h: ora zero page]----------------------------------------------------}
@OPCODE05:     MOV   WORD PTR [INSTRCYCLES],$1003+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               OR    BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[06h: asl zero page]----------------------------------------------------}
@OPCODE06:     MOV   WORD PTR [INSTRCYCLES],$1105+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               SHL   BYTE PTR [DI],1
               JMP   @UPDATECNZ

{---[08h: php implied]------------------------------------------------------}
@OPCODE08:     MOV   WORD PTR [INSTRCYCLES],$0903
               AND   BP,$00FF
               MOV   BYTE PTR [DS:BP+STACKBASE],BH
               DEC   BP
               JMP   @NEXTOPC

{---[09h: ora immediate]----------------------------------------------------}
@OPCODE09:     MOV   WORD PTR [INSTRCYCLES],$0B02+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               OR    BL,AL
               JMP   @UPDATENZ

{---[0Ah: asl accumulator]--------------------------------------------------}
@OPCODE0A:     MOV   WORD PTR [INSTRCYCLES],$0802+$0F00
               SHL   BL,1
               JMP   @UPDATECNZ

{---[0Ch: tsb absolute]-----------------------------------------------------}
@OPCODE0C:     MOV   WORD PTR [INSTRCYCLES],$1206+$0F00
               MOV   DI,WORD PTR [SI]
               ADD   SI,+$02
               TEST  BL,BYTE PTR [DI]
               LAHF
               CMP   DI,$A000
               JAE   @OPC0C_1
               OR    BYTE PTR [DI],BL
@OPC0C_1:      AND   BH,11111101b
               AND   AH,01000000b
               SHR   AH,5
               OR    BH,AH {zero flag}
               JMP   @NEXTOPC

{---[0Dh: ora absolute]-----------------------------------------------------}
@OPCODE0D:     MOV   WORD PTR [INSTRCYCLES],$0E04+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               MOV   DI,AX
               OR    BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[0Eh: asl absolute]-----------------------------------------------------}
@OPCODE0E:     MOV   WORD PTR [INSTRCYCLES],$1306+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
@ASL_ABS:      MOV   DI,AX
               AND   AH,$F0
               CMP   AH,$A0
               JAE   @OPC0E_1
               SHL   BYTE PTR [DI],1
               CALL  UPDATEGRAPH
               JMP   @UPDATECNZ
@OPC0E_1:      CMP   DI,SCHAKELBYTE
               JZ    @OPC0E_2
               MOV   AL,BYTE PTR [DI]
               SHL   AL,1
               JMP   @UPDATECNZ
@OPC0E_2:      CALL  SAVEZP90
               SHL   BYTE PTR [DI],1
               PUSHF
               CALL  SETA000MEM
               POPF
               JMP   @UPDATECNZ

{---[10h: bpl relative]-----------------------------------------------------}
@OPCODE10:     MOV   AL,BH
               SHL   AL,1 {get negative}
               JC    @OPC10_1
               MOV   WORD PTR [INSTRCYCLES],$1303
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CBW
               ADD   SI,AX
               JMP   @NEXTOPC
@OPC10_1:      MOV   WORD PTR [INSTRCYCLES],$0E02
               INC   SI
               JMP   @NEXTOPC

{---[11h: ora (indirect),y]-------------------------------------------------}
@OPCODE11:     MOV   WORD PTR [INSTRCYCLES],$1705+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   AX,WORD PTR [DI]
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               MOV   DI,AX
               OR    BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[12h: ora (indirect)]---------------------------------------------------}
@OPCODE12:     MOV   WORD PTR [INSTRCYCLES],$1305+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   DI,WORD PTR [DI] {get address from atom memory}
               OR    BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[14h: trb zero page]----------------------------------------------------}
@OPCODE14:     MOV   WORD PTR [INSTRCYCLES],$1405+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               TEST  BL,BYTE PTR [DI]
               LAHF
               MOV   AL,BL
               NOT   AL
               AND   BYTE PTR [DI],AL
               AND   BH,11111101b
               AND   AH,01000000b
               SHR   AH,5
               OR    BH,AH {zero flag}
               JMP   @NEXTOPC

{---[15h: ora zero page,x]--------------------------------------------------}
@OPCODE15:     MOV   WORD PTR [INSTRCYCLES],$1104+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               OR    BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[16h: asl zero page,x]--------------------------------------------------}
@OPCODE16:     MOV   WORD PTR [INSTRCYCLES],$1306+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               SHL   BYTE PTR [DI],1
               JMP   @UPDATECNZ

{---[18h: clc]--------------------------------------------------------------}
@OPCODE18:     MOV   WORD PTR [INSTRCYCLES],$0802
               AND   BH,11111110b
               JMP   @NEXTOPC

{---[19h: ora absolute,y]---------------------------------------------------}
@OPCODE19:     MOV   WORD PTR [INSTRCYCLES],$1104+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               MOV   DI,AX
               OR    BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[1Ah: inc accumulator]--------------------------------------------------}
@OPCODE1A:     MOV   WORD PTR [INSTRCYCLES],$1406+$0F00
               INC   BL
               JMP   @UPDATENZ

{---[1Bh: tas implied]------------------------------------------------------}
@OPCODE1B:     MOV   WORD PTR [INSTRCYCLES],$0902
               MOV   AL,BL
               MOV   AH,$00
               MOV   BP,AX
               JMP   @NEXTOPC

{---[1Ch: trb absolute]-----------------------------------------------------}
@OPCODE1C:     MOV   WORD PTR [INSTRCYCLES],$1406+$0F00
               MOV   DI,WORD PTR [SI]
               ADD   SI,+$02
               TEST  BL,BYTE PTR [DI]
               LAHF
               CMP   DI,$A000
               JAE   @OPC1C_1
               MOV   AL,BL
               NOT   AL
               AND   BYTE PTR [DI],AL
@OPC1C_1:      AND   BH,11111101b
               AND   AH,01000000b
               SHR   AH,5
               OR    BH,AH {zero flag}
               JMP   @NEXTOPC

{---[1Dh: ora absolute,x]---------------------------------------------------}
@OPCODE1D:     MOV   WORD PTR [INSTRCYCLES],$1104+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               MOV   DI,AX
               OR    BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[1Eh: asl absolute,x]---------------------------------------------------}
@OPCODE1E:     MOV   WORD PTR [INSTRCYCLES],$1707+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               JMP   @ASL_ABS

{---[20h: jsr absolute]-----------------------------------------------------}
@OPCODE20:     MOV   WORD PTR [INSTRCYCLES],$1306
               MOV   AX,SI
               INC   AX
               AND   BP,$00FF
               MOV   BYTE PTR [DS:BP+STACKBASE],AH
               DEC   BP
               AND   BP,$00FF
               MOV   BYTE PTR [DS:BP+STACKBASE],AL
               DEC   BP
               MOV   SI,WORD PTR [SI]
               JMP   @NEXTOPC

{---[21h: and (indirect,x)]-------------------------------------------------}
@OPCODE21:     MOV   WORD PTR [INSTRCYCLES],$1406+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   DI,WORD PTR [DI] {get address from atom memory}
               AND   BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[22h: nop zero page]----------------------------------------------------}
@OPCODE22:
@OPCODE42:
@OPCODE44:
@OPCODE54:
@OPCODE62:
@OPCODE82:
@OPCODEC2:
@OPCODED4:
@OPCODEE2:
@OPCODEF4:     MOV   WORD PTR [INSTRCYCLES],$0803
               INC   SI
               JMP   @NEXTOPC

{---[24h: bit zero page]----------------------------------------------------}
@OPCODE24:     MOV   WORD PTR [INSTRCYCLES],$1C03
               MOV   AL,BYTE PTR [SI]
               INC   SI
@OPC24_1:      MOV   AH,$00
               MOV   DI,AX
               MOV   AL,BYTE PTR [DI]
               MOV   AH,AL
               AND   BH,00111101b
               AND   AH,11000000b
               OR    BH,AH {get m6, m7 in flags}
               TEST  BL,AL {a & m}
               LAHF
               AND   AH,01000000b
               SHR   AH,5
               OR    BH,AH
               JMP   @NEXTOPC

{---[25h: and zero page]----------------------------------------------------}
@OPCODE25:     MOV   WORD PTR [INSTRCYCLES],$1003+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               AND   BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[26h: rol zero page]----------------------------------------------------}
@OPCODE26:     MOV   WORD PTR [INSTRCYCLES],$1105+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   AL,BH
               SHR   AL,1 {get carry}
               RCL   BYTE PTR [DI],1
               JC    @OPC26_1
               OR    BYTE PTR [DI],$00
               CLC
               JMP   @UPDATECNZ
@OPC26_1:      OR    BYTE PTR [DI],$00
               STC
               JMP   @UPDATECNZ

{---[28h: plp implied]------------------------------------------------------}
@OPCODE28:     MOV   WORD PTR [INSTRCYCLES],$0C04
               CMP   SI,$CFAE
               JNZ   @OPC28_1
               {---finfoutcmd preparation---}
               MOV   WORD PTR @FILENAMEOFS,$0140
               TEST  BH,$01 {test carry}
               JZ    @OPC28_1
               PUSH  BX
               MOV   BL,BYTE PTR [$0004]
               MOV   BH,$00
               MOV   AL,BYTE PTR [BX+$0016]
               MOV   AH,BYTE PTR [BX+$0025]
               MOV   WORD PTR @FILENAMEOFS,AX
               POP   BX
@OPC28_1:      INC   BP
               AND   BP,$00FF
               MOV   BH,BYTE PTR [DS:BP+STACKBASE]
               JMP   @NEXTOPC

{---[29h: and immediate]----------------------------------------------------}
@OPCODE29:     MOV   WORD PTR [INSTRCYCLES],$0B02+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               AND   BL,AL
               JMP   @UPDATENZ

{---[2Ah: rol accumulator]--------------------------------------------------}
@OPCODE2A:     MOV   WORD PTR [INSTRCYCLES],$0802+$0F00
               MOV   AL,BH
               SHR   AL,1 {get carry}
               RCL   BL,1
               JC    @OPC2A_1
               OR    BL,BL
               CLC
               JMP   @UPDATECNZ
@OPC2A_1:      OR    BL,BL
               STC
               JMP   @UPDATECNZ

{---[2Ch: bit absolute]-----------------------------------------------------}
@OPCODE2C:     MOV   WORD PTR [INSTRCYCLES],$2304
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
@OPC2C_4:      MOV   DI,AX
               MOV   AL,AH
               AND   AL,$F0
               CMP   AL,$B0
               JNZ   @OPC2C_2
               CMP   DI,$B001
               JB    @OPC2C_2
               JZ    @BIT_B001
               CMP   DI,$B003
               JB    @BIT_B002
               JZ    @BIT_B003
               CMP   AH,$B8
               JZ    @BIT_VIA
               CMP   AH,$BA
               JZ    @OPC2C_3
@OPC2C_2:      MOV   AL,BYTE PTR [DI]
               JMP   @OPC2C_1
@BIT_B001:     CALL  @L_B001_1
               JMP   @OPC2C_1
@BIT_B002:     CALL  @L_B002_1
               JMP   @OPC2C_1
@BIT_B003:     CALL  @L_B003_1
@OPC2C_1:      MOV   AH,AL
               AND   BH,00111101b
               AND   AH,11000000b
               OR    BH,AH {get m6, m7 in flags}
               TEST  BL,AL {a & m}
               LAHF
               AND   AH,01000000b
               SHR   AH,5
               OR    BH,AH
               JMP   @NEXTOPC
@OPC2C_3:      CALL  READ_FDC
               JMP   @OPC2C_1

{---[2Dh: and absolute]-----------------------------------------------------}
@OPCODE2D:     MOV   WORD PTR [INSTRCYCLES],$1204+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               MOV   DI,AX
               CMP   AX,$B001
               JB    @OPC2D_1
               JZ    @AND_B001
               CMP   AX,$B003
               JB    @AND_B002
               JZ    @AND_B003
               CMP   AH,$B8
               JZ    @OPC2D_2
               CMP   AH,$BA
               JZ    @OPC2D_3
@OPC2D_1:      AND   BL,BYTE PTR [DI]
               JMP   @UPDATENZ
@AND_B001:     CALL  @L_B001_1
               AND   BL,AL
               JMP   @UPDATENZ
@AND_B002:     CALL  @L_B002_1
               AND   BL,AL
               JMP   @UPDATENZ
@AND_B003:     CALL  @L_B003_1
               AND   BL,AL
               JMP   @UPDATENZ
@OPC2D_2:      CALL  @GETVIAREG
               AND   BL,AL
               JMP   @UPDATENZ
@OPC2D_3:      CALL  READ_FDC
               AND   BL,AL
               JMP   @UPDATENZ

{---[2Eh: rol absolute]-----------------------------------------------------}
@OPCODE2E:     MOV   WORD PTR [INSTRCYCLES],$2306+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               MOV   DI,AX
               AND   AH,$F0
               CMP   AH,$A0
               JAE   @OPC2E_1
               MOV   AL,BH
               SHR   AL,1 {get carry}
               RCL   BYTE PTR [DI],1
               JC    @OPC2E_3
               OR    BYTE PTR [DI],$00
               CLC
               CALL  UPDATEGRAPH
               JMP   @UPDATECNZ
@OPC2E_3:      OR    BYTE PTR [DI],$00
               STC
               CALL  UPDATEGRAPH
               JMP   @UPDATECNZ
@OPC2E_1:      MOV   AL,BH
               SHR   AL,1 {get carry}
               MOV   AL,BYTE PTR [DI]
               RCL   AL,1
               JC    @OPC2E_4
               OR    AL,AL
               CLC
               JMP   @UPDATECNZ
@OPC2E_4:      OR    AL,AL
               STC
               JMP   @UPDATECNZ

{---[30h: bmi relative]-----------------------------------------------------}
@OPCODE30:     MOV   AL,BH
               SHL   AL,1 {get negative}
               JNC   @OPC30_1
               MOV   WORD PTR [INSTRCYCLES],$1303
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CBW
               ADD   SI,AX
               JMP   @NEXTOPC
@OPC30_1:      MOV   WORD PTR [INSTRCYCLES],$0E02
               INC   SI
               JMP   @NEXTOPC

{---[31h: and (indirect),y]-------------------------------------------------}
@OPCODE31:     MOV   WORD PTR [INSTRCYCLES],$1705+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   AX,WORD PTR [DI] {get address from atom memory}
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               MOV   DI,AX
               AND   BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[32h: and (indirect)]---------------------------------------------------}
@OPCODE32:     MOV   WORD PTR [INSTRCYCLES],$1305+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   DI,WORD PTR [DI] {get address from atom memory}
               AND   BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[34h: bit zero page,x]--------------------------------------------------}
@OPCODE34:     MOV   WORD PTR [INSTRCYCLES],$1E04
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               JMP   @OPC24_1

{---[35h: and zero page,x]--------------------------------------------------}
@OPCODE35:     MOV   WORD PTR [INSTRCYCLES],$1104+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               AND   BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[36h: rol zero page,x]--------------------------------------------------}
@OPCODE36:     MOV   WORD PTR [INSTRCYCLES],$1306+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   AL,BH
               SHR   AL,1 {get carry}
               RCL   BYTE PTR [DI],1
               JC    @OPC36_1
               OR    BYTE PTR [DI],$00
               CLC
               JMP   @UPDATECNZ
@OPC36_1:      OR    BYTE PTR [DI],$00
               STC
               JMP   @UPDATECNZ

{---[38h: sec implied]------------------------------------------------------}
@OPCODE38:     MOV   WORD PTR [INSTRCYCLES],$0802
               OR    BH,00000001h
               JMP   @NEXTOPC

{---[39h: and absolute,y]---------------------------------------------------}
@OPCODE39:     MOV   WORD PTR [INSTRCYCLES],$1104+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               MOV   DI,AX
               AND   BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[3Ah: dec accumulator]--------------------------------------------------}
@OPCODE3A:     MOV   WORD PTR [INSTRCYCLES],$0802
               DEC   BL
               JMP   @UPDATENZ

{---[3Bh: tsa implied]------------------------------------------------------}
@OPCODE3B:     MOV   WORD PTR [INSTRCYCLES],$0902+$0F00
               MOV   AX,BP
               MOV   BL,AL
               OR    AL,AL
               JMP   @UPDATENZ

{---[3Ch: bit absolute,x]---------------------------------------------------}
@OPCODE3C:     MOV   WORD PTR [INSTRCYCLES],$2404
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               JMP   @OPC2C_4

{---[3Dh: and absolute,x]---------------------------------------------------}
@OPCODE3D:     MOV   WORD PTR [INSTRCYCLES],$1104+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               MOV   DI,AX
               AND   BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[3Eh: rol absolute,x]---------------------------------------------------}
@OPCODE3E:     MOV   WORD PTR [INSTRCYCLES],$2407+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               MOV   DI,AX
               AND   AH,$F0
               CMP   AH,$A0
               JAE   @OPC3E_1
               MOV   AL,BH
               SHR   AL,1 {get carry}
               RCL   BYTE PTR [DI],1
               JC    @OPC3E_3
               OR    BYTE PTR [DI],$00
               CLC
               CALL  UPDATEGRAPH
               JMP   @UPDATECNZ
@OPC3E_3:      OR    BYTE PTR [DI],$00
               STC
               CALL  UPDATEGRAPH
               JMP   @UPDATECNZ
@OPC3E_1:      MOV   AL,BH
               SHR   AL,1 {get carry}
               MOV   AL,BYTE PTR [DI]
               RCL   AL,1
               JC    @OPC3E_4
               OR    AL,AL
               CLC
               JMP   @UPDATECNZ
@OPC3E_4:      OR    AL,AL
               STC
               JMP   @UPDATECNZ

{---[40h: rti implied]------------------------------------------------------}
@OPCODE40:     MOV   WORD PTR [INSTRCYCLES],$1706
               CMP   BYTE PTR [CS:AANTBOXRET],$00
               JZ    @OPC40_1
               PUSH  BX
               MOV   BL,BYTE PTR [CS:AANTBOXRET]
               DEC   BL
               MOV   BH,$00
               SHL   BX,1
               MOV   AX,BP
               DEC   AL {ivm met PHA voor ind. jmp, bij zowel IRQ als NMI}
               CMP   AL,BYTE PTR BOXRETURNS[CS:BX+$01]
               MOV   AL,BYTE PTR BOXRETURNS[CS:BX]
               POP   BX
               JNZ   @OPC40_1
               {---return to previous box---}
               DEC   BYTE PTR [CS:AANTBOXRET]
               PUSH  AX
               CALL  SAVEZP90
               POP   AX
               MOV   BYTE PTR [SCHAKELBYTE],AL
               CALL  SETA000MEM
@OPC40_1:      INC   BP
               AND   BP,$00FF
               MOV   BH,BYTE PTR [DS:BP+STACKBASE]
               INC   BP
               AND   BP,$00FF
               MOV   AL,BYTE PTR [DS:BP+STACKBASE]
               INC   BP
               AND   BP,$00FF
               MOV   AH,BYTE PTR [DS:BP+STACKBASE]
               MOV   SI,AX
               JMP   @NEXTOPC

{---[41h: eor (indirect,x)]-------------------------------------------------}
@OPCODE41:     MOV   WORD PTR [INSTRCYCLES],$1406+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   DI,WORD PTR [DI] {get address from atom memory}
               XOR   BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[45h: eor zero page]----------------------------------------------------}
@OPCODE45:     MOV   WORD PTR [INSTRCYCLES],$1003+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               XOR   BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[46h: lsr zero page]----------------------------------------------------}
@OPCODE46:     MOV   WORD PTR [INSTRCYCLES],$1105+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               SHR   BYTE PTR [DI],1
               JMP   @UPDATECNZ

{---[48h: pha implied]------------------------------------------------------}
@OPCODE48:     MOV   WORD PTR [INSTRCYCLES],$0903
               AND   BP,$00FF
               MOV   BYTE PTR [DS:BP+STACKBASE],BL
               DEC   BP
               JMP   @NEXTOPC

{---[49h: eor immediate]----------------------------------------------------}
@OPCODE49:     MOV   WORD PTR [INSTRCYCLES],$0B02+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               XOR   BL,AL
               JMP   @UPDATENZ

{---[4Ah: lsr accumulator]--------------------------------------------------}
@OPCODE4A:     MOV   WORD PTR [INSTRCYCLES],$0802+$0F00
               SHR   BL,1
               JMP   @UPDATECNZ

{---[4Ch: jmp absolute]-----------------------------------------------------}
@OPCODE4C:     MOV   WORD PTR [INSTRCYCLES],$1003
               CMP   SI,WORD PTR [CS:ABLOKSPRONG]
               JZ    @OPC4C_1
@OPC4C_2:      MOV   SI,WORD PTR [SI]
               JMP   @NEXTOPC
@OPC4C_1:      TEST  BYTE PTR [CS:BOXSWITCH],$FF
               JZ    @OPC4C_2
               MOV   AL,BYTE PTR [SCHAKELBYTE]
               AND   AL,$0F
               MOV   BYTE PTR @SCHAKELSTART,AL
               CMP   WORD PTR [$A000],$BF40
               JNZ   @OPC4C_3
@OPC4C_4:      MOV   BP,$00FF
               MOV   SI,$A002
               JMP   @NEXTOPC
@OPC4C_3:      CALL  SAVEZP90
               INC   BYTE PTR [SCHAKELBYTE]
               AND   BYTE PTR [SCHAKELBYTE],$0F
               PUSH  ES
               MOV   AX,DS
               ADD   AX,$1000
               MOV   ES,AX
               MOV   AL,$00
               MOV   AH,BYTE PTR SCHAKELBYTE
               SHL   AH,4
               MOV   DI,AX
               CMP   WORD PTR [ES:DI],$BF40
               POP   ES
               JNZ   @OPC4C_5
               CALL  SETA000MEM
               MOV   AL,BYTE PTR [SCHAKELBYTE]
               CMP   AL,BYTE PTR @SCHAKELSTART
               JNZ   @OPC4C_4
               JMP   @JMPTOBRK
@OPC4C_5:      MOV   AL,BYTE PTR [SCHAKELBYTE]
               CMP   AL,BYTE PTR @SCHAKELSTART
               JNZ   @OPC4C_3
               CALL  SETA000MEM
               JMP   @JMPTOBRK

{---[schakel_brk]-----------------------------------------------------------}
@SCHAKEL_BRK:  PUSH  BX
               MOV   BX,BP
               ADD   BL,$02
               AND   BX,$00FF
               CMP   BYTE PTR [BX+STACKBASE],+94
               POP   BX
               JZ    @OPC4C_3
@JMPTOBRK:     MOV   AX,WORD PTR [$0202]
               AND   AH,$F0
               CMP   AH,$A0
               JNZ   @JMPBRK1
               PUSH  ES
               MOV   AX,DS
               ADD   AX,$2000
               MOV   ES,AX
               MOV   AL,BYTE PTR [ES:$0122]
               POP   ES
               MOV   AH,BYTE PTR [SCHAKELBYTE]
               AND   AX,$0F0F
               CMP   AL,AH
               JZ    @JMPBRK1
               CALL  SAVEZP90
               PUSH  ES
               MOV   AX,DS
               ADD   AX,$2000
               MOV   ES,AX
               MOV   AL,BYTE PTR [ES:$0122]
               POP   ES
               MOV   BYTE PTR [SCHAKELBYTE],AL
               CALL  SETA000MEM
@JMPBRK1:      MOV   SI,WORD PTR [$0202]
               JMP   @NEXTOPC

{---[4Dh: eor absolute]-----------------------------------------------------}
@OPCODE4D:     MOV   WORD PTR [INSTRCYCLES],$0E04+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               MOV   DI,AX
               XOR   BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[4Eh: lsr absolute]-----------------------------------------------------}
@OPCODE4E:     MOV   WORD PTR [INSTRCYCLES],$1306+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
@LSR_ABS:      MOV   DI,AX
               AND   AH,$F0
               CMP   AH,$A0
               JAE   @OPC4E_1
               SHR   BYTE PTR [DI],1
               CALL  UPDATEGRAPH
               JMP   @UPDATECNZ
@OPC4E_1:      CMP   DI,SCHAKELBYTE
               JZ    @OPC4E_2
               MOV   AL,BYTE PTR [DI]
               SHR   AL,1
               JMP   @UPDATECNZ
@OPC4E_2:      CALL  SAVEZP90
               SHR   BYTE PTR [DI],1
               PUSHF
               CALL  SETA000MEM
               POPF
               JMP   @UPDATECNZ

{---[50h: bvc relative]-----------------------------------------------------}
@OPCODE50:     MOV   AL,BH
               SHL   AL,2 {get overflow}
               JC    @OPC50_1
               MOV   WORD PTR [INSTRCYCLES],$1303
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CBW
               ADD   SI,AX
               JMP   @NEXTOPC
@OPC50_1:      MOV   WORD PTR [INSTRCYCLES],$0E02
               INC   SI
               JMP   @NEXTOPC

{---[51h: eor (indirect),y]-------------------------------------------------}
@OPCODE51:     MOV   WORD PTR [INSTRCYCLES],$1705+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   AX,WORD PTR [DI] {get address from atom memory}
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               MOV   DI,AX
               XOR   BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[52h: eor (indirect)]---------------------------------------------------}
@OPCODE52:     MOV   WORD PTR [INSTRCYCLES],$1305+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   DI,WORD PTR [DI]
               XOR   BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[55h: eor zero page,x]--------------------------------------------------}
@OPCODE55:     MOV   WORD PTR [INSTRCYCLES],$1104+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               XOR   BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[56h: lsr zero page,x]--------------------------------------------------}
@OPCODE56:     MOV   WORD PTR [INSTRCYCLES],$1306+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               SHR   BYTE PTR [DI],1
               JMP   @UPDATECNZ

{---[58h: cli]--------------------------------------------------------------}
@OPCODE58:     MOV   WORD PTR [INSTRCYCLES],$0802
               AND   BH,11111011b
               JMP   @NEXTOPC

{---[59h: eor absolute,y]---------------------------------------------------}
@OPCODE59:     MOV   WORD PTR [INSTRCYCLES],$1104+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               MOV   DI,AX
               XOR   BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[5Ah: phy implied]------------------------------------------------------}
@OPCODE5A:     MOV   WORD PTR [INSTRCYCLES],$0903
               AND   BP,$00FF
               MOV   BYTE PTR [DS:BP+STACKBASE],DL
               DEC   BP
               JMP   @NEXTOPC

{---[5Ch: nop absolute]-----------------------------------------------------}
@OPCODE5C:
@OPCODEDC:     MOV   WORD PTR [INSTRCYCLES],$0804
               ADD   SI,+$02
               JMP   @NEXTOPC


{---[5Dh: eor absolute,x]---------------------------------------------------}
@OPCODE5D:     MOV   WORD PTR [INSTRCYCLES],$1104+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               MOV   DI,AX
               XOR   BL,BYTE PTR [DI]
               JMP   @UPDATENZ

{---[5Eh: lsr absolute,x]---------------------------------------------------}
@OPCODE5E:     MOV   WORD PTR [INSTRCYCLES],$1707+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               JMP   @LSR_ABS

{---[60h: rts implied]------------------------------------------------------}
@OPCODE60:     MOV   WORD PTR [INSTRCYCLES],$1406
               CMP   BYTE PTR [CS:AANTBOXRET],$00
               JZ    @OPC60_1
               PUSH  BX
               MOV   BL,BYTE PTR [CS:AANTBOXRET]
               DEC   BL
               MOV   BH,$00
               SHL   BX,1
               MOV   AX,BP
               CMP   AL,BYTE PTR BOXRETURNS[CS:BX+$01]
               MOV   AL,BYTE PTR BOXRETURNS[CS:BX]
               POP   BX
               JNZ   @OPC60_1
               {---return to previous box---}
               DEC   BYTE PTR [CS:AANTBOXRET]
               PUSH  AX
               CALL  SAVEZP90
               POP   AX
               MOV   BYTE PTR [SCHAKELBYTE],AL
               CALL  SETA000MEM
@OPC60_1:      INC   BP
               AND   BP,$00FF
               MOV   AL,BYTE PTR [DS:BP+STACKBASE]
               INC   BP
               AND   BP,$00FF
               MOV   AH,BYTE PTR [DS:BP+STACKBASE]
               INC   AX
               MOV   SI,AX
               JMP   @NEXTOPC

{---[61h: adc (indirect,x)]-------------------------------------------------}
@OPCODE61:     MOV   WORD PTR [INSTRCYCLES],$1E06+$1400
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   DI,WORD PTR [DI] {get address from atom memory}
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @ADC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               ADC   BL,AL
               JMP   @UPDATECVNZ

{---[64h: stz zero page]----------------------------------------------------}
@OPCODE64:     MOV   WORD PTR [INSTRCYCLES],$0F03
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   BYTE PTR [DI],$00
               JMP   @NEXTOPC

{---[65h: adc zero page]----------------------------------------------------}
@OPCODE65:     MOV   WORD PTR [INSTRCYCLES],$1A03+$1400
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @ADC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               ADC   BL,AL
               JMP   @UPDATECVNZ

{---[66h: ror zero page]----------------------------------------------------}
@OPCODE66:     MOV   WORD PTR [INSTRCYCLES],$1105+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   AL,BH
               SHR   AL,1 {get carry}
               RCR   BYTE PTR [DI],1
               JC    @OPC66_1
               OR    BYTE PTR [DI],$00
               CLC
               JMP   @UPDATECNZ
@OPC66_1:      OR    BYTE PTR [DI],$00
               STC
               JMP   @UPDATECNZ

{---[68h: pla implied]------------------------------------------------------}
@OPCODE68:     MOV   WORD PTR [INSTRCYCLES],$0904+$0F00
               INC   BP
               AND   BP,$00FF
               MOV   BL,BYTE PTR [DS:BP+STACKBASE]
               OR    BL,BL
               JMP   @UPDATENZ

{---[69h: adc immediate]----------------------------------------------------}
@OPCODE69:     MOV   WORD PTR [INSTRCYCLES],$1502+$1400
               MOV   AL,BYTE PTR [SI]
               INC   SI
               TEST  BH,00001000b
               JNZ   @ADC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               ADC   BL,AL
               JMP   @UPDATECVNZ

{---[6Ah: ror accumulator]--------------------------------------------------}
@OPCODE6A:     MOV   WORD PTR [INSTRCYCLES],$0802+$0F00
               MOV   AL,BH
               SHR   AL,1 {get carry}
               RCR   BL,1
               JC    @OPC6A_1
               OR    BL,BL
               CLC
               JMP   @UPDATECNZ
@OPC6A_1:      OR    BL,BL
               STC
               JMP   @UPDATECNZ

{---[6Ch: jmp (absolute indirect)]------------------------------------------}
@OPCODE6C:     MOV   WORD PTR [INSTRCYCLES],$4005
               MOV   SI,WORD PTR [SI]
               MOV   AX,WORD PTR [SI]
               CMP   SI,LOADVEC
               JNZ   @OPC6C_9
               CMP   AX,WORD PTR [$FFA2]
               JNZ   @OPC6C_2
               JMP   @LOADFILE
@OPC6C_9:      CMP   SI,SAVEVEC
               JNZ   @OPC6C_10
               CMP   AX,WORD PTR [$FFA4]
               JNZ   @OPC6C_2
               JMP   @SAVEFILE
@OPC6C_10:     CMP   SI,GETBYTEVEC
               JNZ   @OPC6C_11
               CMP   AX,WORD PTR [$FFAA]
               JNZ   @OPC6C_2
               JMP   @GETBYTE
@OPC6C_11:     CMP   SI,PUTBYTEVEC
               JNZ   @OPC6C_12
               CMP   AX,WORD PTR [$FFAC]
               JNZ   @OPC6C_2
               JMP   @PUTBYTE
@OPC6C_12:     CMP   SI,FINDVEC
               JNZ   @OPC6C_1
               AND   BP,$00FF
               CMP   WORD PTR [DS:BP+STACKBASE+1],$CFB0
               JNZ   @OPC6C_2
               CMP   AX,WORD PTR [$FFAE]
               JNZ   @OPC6C_2
               JMP   @FINFOUTCMD
@OPC6C_1:      CMP   SI,$00C9
               JNZ   @OPC6C_2
               MOV   SI,WORD PTR [SI]
               CMP   SI,$FA2A
               JZ    @TAPECAT
               JMP   @NEXTOPC
@OPC6C_2:      CMP   SI,$0200
               JB    @OPC6C_4
               CMP   SI,$021C
               JAE   @OPC6C_6
               CMP   SI,$0202
               JNZ   @OPC6C_8
               TEST  BYTE PTR [CS:BOXSWITCH],$FF
               JZ    @OPC6C_4
               JMP   @SCHAKEL_BRK
@OPC6C_6:      CMP   SI,$03FE
               JNZ   @OPC6C_4
               AND   AH,$F0
               CMP   AH,$A0
               JNZ   @OPC6C_4
               MOV   DI,$001C
               JMP   @OPC6C_3
@OPC6C_8:      MOV   AX,WORD PTR [SI]
               AND   AH,$F0
               CMP   AH,$A0
               JNZ   @OPC6C_4
               MOV   DI,SI
               AND   DI,$00FF
@OPC6C_3:      PUSH  ES
               MOV   AX,DS
               ADD   AX,$2000
               MOV   ES,AX
               MOV   AL,BYTE PTR [ES:DI+$0120]
               POP   ES
@OPC6C_7:      MOV   AH,BYTE PTR [SCHAKELBYTE]
               AND   AX,$0F0F
               CMP   AL,AH
               JZ    @OPC6C_4
               CMP   BYTE PTR [CS:AANTBOXRET],$20
               JAE   @OPC6C_5
               {---jump into another box than currently at A000h---}
               PUSH  DI
               PUSH  AX
               CALL  SAVEZP90
               POP   AX
               POP   DI
               PUSH  BX
               MOV   BL,BYTE PTR [CS:AANTBOXRET]
               MOV   BH,$00
               SHL   BX,1
               MOV   BYTE PTR BOXRETURNS[CS:BX],AH
               MOV   AX,BP
               MOV   BYTE PTR BOXRETURNS[CS:BX+$01],AL
               INC   BYTE PTR [CS:AANTBOXRET]
               POP   BX
               PUSH  ES
               MOV   AX,DS
               ADD   AX,$2000
               MOV   ES,AX
               MOV   AL,BYTE PTR [ES:$0120+DI]
               POP   ES
               MOV   BYTE PTR [SCHAKELBYTE],AL
               CALL  SETA000MEM
@OPC6C_4:      MOV   SI,WORD PTR [SI]
               JMP   @NEXTOPC
@OPC6C_5:      {---too many calls from one box to other; generate error 33---}
               MOV   BYTE PTR [CS:AANTBOXRET],$00
               MOV   SI,+32
               JMP   @OPCODE00

{---[6Dh: adc absolute]-----------------------------------------------------}
@OPCODE6D:     MOV   WORD PTR [INSTRCYCLES],$1804+$1400
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               MOV   DI,AX
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @ADC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               ADC   BL,AL
               JMP   @UPDATECVNZ

{---[6Eh: ror absolute]-----------------------------------------------------}
@OPCODE6E:     MOV   WORD PTR [INSTRCYCLES],$2306+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               MOV   DI,AX
               AND   AH,$F0
               CMP   AH,$A0
               JAE   @OPC6E_1
               MOV   AL,BH
               SHR   AL,1 {get carry}
               RCR   BYTE PTR [DI],1
               JC    @OPC6E_3
               OR    BYTE PTR [DI],$00
               CLC
               CALL  UPDATEGRAPH
               JMP   @UPDATECNZ
@OPC6E_3:      OR    BYTE PTR [DI],$00
               STC
               CALL  UPDATEGRAPH
               JMP   @UPDATECNZ
@OPC6E_1:      MOV   AL,BH
               SHR   AL,1 {get carry}
               MOV   AL,BYTE PTR [DI]
               RCR   AL,1
               JC    @OPC6E_4
               OR    AL,AL
               CLC
               JMP   @UPDATECNZ
@OPC6E_4:      OR    AL,AL
               STC
               JMP   @UPDATECNZ

{---[adc_dec]---------------------------------------------------------------}
@ADC_DEC:      MOV   AH,BH
               SHR   AH,1 {get carry}
               ADC   AL,BL
               JO    @ADCDEC1
               DAA
               LAHF
               MOV   BL,AL
               AND   BH,10111111b {clear overflow}
               SAHF
               JMP   @UPDATECNZ
@ADCDEC1:      DAA
               LAHF
               MOV   BL,AL
               OR    BH,01000000b {set overflow}
               SAHF
               JMP   @UPDATECNZ

{---[70h: bvs relative]-----------------------------------------------------}
@OPCODE70:     MOV   AL,BH
               SHL   AL,2 {get overflow}
               JNC   @OPC70_1
               MOV   WORD PTR [INSTRCYCLES],$1303
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CBW
               ADD   SI,AX
               JMP   @NEXTOPC
@OPC70_1:      MOV   WORD PTR [INSTRCYCLES],$0E02
               INC   SI
               JMP   @NEXTOPC

{---[71h: adc (indirect),y]-------------------------------------------------}
@OPCODE71:     MOV   WORD PTR [INSTRCYCLES],$2105+$1400
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   AX,WORD PTR [DI] {get address from atom memory}
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               MOV   DI,AX
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @ADC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               ADC   BL,AL
               JMP   @UPDATECVNZ

{---[72h: adc (indirect)]---------------------------------------------------}
@OPCODE72:     MOV   WORD PTR [INSTRCYCLES],$1D05+$1400
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   DI,WORD PTR [DI] {get address from atom memory}
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @ADC_DEC
               MOV   AH,BH
               SHR   AH,1
               ADC   BL,AL
               JMP   @UPDATECVNZ

{---[74h: stz zero page,x]--------------------------------------------------}
@OPCODE74:     MOV   WORD PTR [INSTRCYCLES],$1004
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   BYTE PTR [DI],$00
               JMP   @NEXTOPC

{---[75h: adc zero page,x]--------------------------------------------------}
@OPCODE75:     MOV   WORD PTR [INSTRCYCLES],$1B04+$1400
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @ADC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               ADC   BL,AL
               JMP   @UPDATECVNZ

{---[76h: ror zero page,x]--------------------------------------------------}
@OPCODE76:     MOV   WORD PTR [INSTRCYCLES],$1306+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   AL,BH
               SHR   AL,1 {get carry}
               RCR   BYTE PTR [DI],1
               JC    @OPC76_1
               OR    BYTE PTR [DI],$00
               CLC
               JMP   @UPDATECNZ
@OPC76_1:      OR    BYTE PTR [DI],$00
               STC
               JMP   @UPDATECNZ

{---[78h: sei]--------------------------------------------------------------}
@OPCODE78:     MOV   WORD PTR [INSTRCYCLES],$0802
               OR    BH,00000100b
               JMP   @NEXTOPC

{---[79h: adc absolute,y]---------------------------------------------------}
@OPCODE79:     MOV   WORD PTR [INSTRCYCLES],$1B04+$1400
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               MOV   DI,AX
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @ADC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               ADC   BL,AL
               JMP   @UPDATECVNZ

{---[7Ah: ply implied]------------------------------------------------------}
@OPCODE7A:     MOV   WORD PTR [INSTRCYCLES],$0904+$0F00
               INC   BP
               AND   BP,$00FF
               MOV   DL,BYTE PTR [DS:BP+STACKBASE]
               OR    DL,DL
               JMP   @UPDATENZ

{---[7Ch: jmp (absolute,x)]-------------------------------------------------}
@OPCODE7C:     MOV   WORD PTR [INSTRCYCLES],$0806
               MOV   AX,WORD PTR [SI]
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               MOV   SI,AX
               MOV   SI,WORD PTR [SI]
               JMP   @NEXTOPC

{---[7Dh: adc absolute,x]---------------------------------------------------}
@OPCODE7D:     MOV   WORD PTR [INSTRCYCLES],$1B04+$1400
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               MOV   DI,AX
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @ADC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               ADC   BL,AL
               JMP   @UPDATECVNZ

{---[7Eh: ror absolute,x]---------------------------------------------------}
@OPCODE7E:     MOV   WORD PTR [INSTRCYCLES],$2407+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               MOV   DI,AX
               AND   AH,$F0
               CMP   AH,$A0
               JAE   @OPC7E_1
               MOV   AL,BH
               SHR   AL,1 {get carry}
               RCR   BYTE PTR [DI],1
               JC    @OPC7E_3
               OR    BYTE PTR [DI],$00
               CLC
               CALL  UPDATEGRAPH
               JMP   @UPDATECNZ
@OPC7E_3:      OR    BYTE PTR [DI],$00
               STC
               CALL  UPDATEGRAPH
               JMP   @UPDATECNZ
@OPC7E_1:      MOV   AL,BH
               SHR   AL,1 {get carry}
               MOV   AL,BYTE PTR [DI]
               RCR   AL,1
               JC    @OPC7E_4
               OR    AL,AL
               CLC
               JMP   @UPDATECNZ
@OPC7E_4:      OR    AL,AL
               STC
               JMP   @UPDATECNZ

{---[80h: bra relative]-----------------------------------------------------}
@OPCODE80:     MOV   WORD PTR [INSTRCYCLES],$0803
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CBW
               ADD   SI,AX
               JMP   @NEXTOPC

{---[81h: sta (indirect,x)]-------------------------------------------------}
@OPCODE81:     MOV   WORD PTR [INSTRCYCLES],$2506
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   AX,WORD PTR [DI] {get address from atom memory}
               JMP   @STORE_A

{---[84h: sty zero page]----------------------------------------------------}
@OPCODE84:     MOV   WORD PTR [INSTRCYCLES],$0F03
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   BYTE PTR [DI],DL
               JMP   @NEXTOPC

{---[85h: sta zero page]----------------------------------------------------}
@OPCODE85:     MOV   WORD PTR [INSTRCYCLES],$0F03
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   BYTE PTR [DI],BL
               JMP   @NEXTOPC

{---[86h: stx zero page]----------------------------------------------------}
@OPCODE86:     MOV   WORD PTR [INSTRCYCLES],$0F03
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   BYTE PTR [DI],CL
               JMP   @NEXTOPC

{---[88h: dey implied]------------------------------------------------------}
@OPCODE88:     MOV   WORD PTR [INSTRCYCLES],$0802+$0F00
               DEC   DL
               JMP   @UPDATENZ

{---[89h: bit immediate (only affects zero flag)]---------------------------}
@OPCODE89:     MOV   WORD PTR [INSTRCYCLES],$0B02+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               TEST  BL,AL
               LAHF
               AND   BH,11111101b
               AND   AH,01000000b
               SHR   AH,5
               OR    BH,AH {zero flag}
               JMP   @NEXTOPC

{---[8Ah: txa implied]------------------------------------------------------}
@OPCODE8A:     MOV   WORD PTR [INSTRCYCLES],$0902+$0F00
               MOV   BL,CL
               OR    BL,BL
               JMP   @UPDATENZ

{---[8Ch: sty absolute]-----------------------------------------------------}
@OPCODE8C:     MOV   WORD PTR [INSTRCYCLES],$1F04
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               MOV   DI,AX
               MOV   AL,AH
               AND   AL,$F0
               CMP   AL,$A0
               JB    @OPC8C_2
               CMP   AL,$B0
               JNZ   @OPC8C_3
               CMP   AH,$B0
               JNZ   @OPC8C_4
               CMP   DI,$B000
               JZ    @STY_B000
               CMP   DI,$B002
               JZ    @STY_B002
               CMP   DI,$B003
               JNZ   @OPC8C_3
               JMP   @STY_B003
@OPC8C_4:      CMP   AH,$B8
               JZ    @STY_VIA
               JB    @OPC8C_5
               CMP   AH,$BA
               JNZ   @OPC8C_6
               MOV   AL,DL
               CALL  WRITE_FDC
               JMP   @NEXTOPC
@OPC8C_6:      CMP   DI,$BFE0
               JZ    @STY_MOUSEX
               CMP   DI,$BFE1
               JZ    @STY_MOUSEY
               CMP   DI,$BFE2
               JNZ   @OPC8C_1
               MOV   AL,DL
               JMP   @STORE_MOUSENR
@OPC8C_1:      CMP   DI,SCHAKELBYTE
               JNZ   @OPC8C_3
               CALL  SAVEZP90
               MOV   BYTE PTR [DI],DL
               CALL  SETA000MEM
               JMP   @NEXTOPC
@OPC8C_2:      MOV   BYTE PTR [DI],DL
               CALL  UPDATEGRAPH
@OPC8C_3:      JMP   @NEXTOPC
@OPC8C_5:      CMP   AH,$B4
               JB    @OPC8C_3
               MOV   AL,DL
               PUSH  DX
               MOV   DX,DI
               AND   DX,$03FF
               OUT   DX,AL
               POP   DX
               JMP   @NEXTOPC


{---[8Dh: sta absolute]-----------------------------------------------------}
@OPCODE8D:     MOV   WORD PTR [INSTRCYCLES],$1F04
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
@STORE_A:      MOV   DI,AX
               MOV   AL,AH
               AND   AL,$F0
               CMP   AL,$A0
               JB    @OPC8D_2
               CMP   AL,$B0
               JNZ   @OPC8D_3
               CMP   AH,$B0
               JNZ   @OPC8D_4
               CMP   DI,$B000
               JZ    @STA_B000
               CMP   DI,$B002
               JZ    @STA_B002
               CMP   DI,$B003
               JNZ   @OPC8D_3
               JMP   @STA_B003
@OPC8D_4:      CMP   AH,$B8
               JZ    @STA_VIA
               JB    @OPC8D_5
               CMP   AH,$BA
               JNZ   @OPC8D_6
               MOV   AL,BL
               CALL  WRITE_FDC
               JMP   @NEXTOPC
@OPC8D_6:      CMP   DI,$BFE0
               JZ    @STA_MOUSEX
               CMP   DI,$BFE1
               JZ    @STA_MOUSEY
               CMP   DI,$BFE2
               JNZ   @OPC8D_1
               MOV   AL,BL
               JMP   @STORE_MOUSENR
@OPC8D_1:      CMP   DI,SCHAKELBYTE
               JNZ   @OPC8D_3
               CALL  SAVEZP90
               MOV   BYTE PTR [DI],BL
               CALL  SETA000MEM
               JMP   @NEXTOPC
@OPC8D_2:      MOV   BYTE PTR [DI],BL
               CALL  UPDATEGRAPH
@OPC8D_3:      JMP   @NEXTOPC
@OPC8D_5:      CMP   AH,$B4
               JB    @OPC8D_3
               MOV   AL,BL
               PUSH  DX
               MOV   DX,DI
               AND   DX,$03FF
               OUT   DX,AL
               POP   DX
               JMP   @NEXTOPC


{---[8Eh: stx absolute]-----------------------------------------------------}
@OPCODE8E:     MOV   WORD PTR [INSTRCYCLES],$1F04
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               MOV   DI,AX
               MOV   AL,AH
               AND   AL,$F0
               CMP   AL,$A0
               JB    @OPC8E_2
               CMP   AL,$B0
               JNZ   @OPC8E_3
               CMP   AH,$B0
               JNZ   @OPC8E_4
               CMP   DI,$B000
               JZ    @STX_B000
               CMP   DI,$B002
               JZ    @STX_B002
               CMP   DI,$B003
               JNZ   @OPC8E_3
               JMP   @STX_B003
@OPC8E_4:      CMP   AH,$B8
               JZ    @STX_VIA
               JB    @OPC8E_5
               CMP   AH,$BA
               JNZ   @OPC8E_6
               MOV   AL,CL
               CALL  WRITE_FDC
               JMP   @NEXTOPC
@OPC8E_6:      CMP   DI,$BFE0
               JZ    @STX_MOUSEX
               CMP   DI,$BFE1
               JZ    @STX_MOUSEY
               CMP   DI,$BFE2
               JNZ   @OPC8E_1
               MOV   AL,CL
               JMP   @STORE_MOUSENR
@OPC8E_1:      CMP   DI,SCHAKELBYTE
               JNZ   @OPC8E_3
               CALL  SAVEZP90
               MOV   BYTE PTR [DI],CL
               CALL  SETA000MEM
               JMP   @NEXTOPC
@OPC8E_2:      MOV   BYTE PTR [DI],CL
               CALL  UPDATEGRAPH
@OPC8E_3:      JMP   @NEXTOPC
@OPC8E_5:      CMP   AH,$B4
               JB    @OPC8E_3
               MOV   AL,CL
               PUSH  DX
               MOV   DX,DI
               AND   DX,$03FF
               OUT   DX,AL
               POP   DX
               JMP   @NEXTOPC

{---[sta/stx/sty/stz_b002]--------------------------------------------------}
@STZ_B002:     MOV   AL,$00
               JMP   @S_B002_1
@STA_B002:     MOV   AL,BL
               JMP   @S_B002_1
@STX_B002:     MOV   AL,CL
               JMP   @S_B002_1
@STY_B002:     MOV   AL,DL
@S_B002_1:     MOV   AH,BYTE PTR [$B002]
               AND   AL,$0F
               AND   BYTE PTR [$B002],$F0
               OR    BYTE PTR [$B002],AL
               PUSH  AX
               AND   AX,$0808
               CMP   AL,AH
               JZ    @S_B002_4
               OR    AL,AL
               JNZ   @S_B002_5
               CMP   BYTE PTR [CS:GRAPHMODE],$05
               JB    @S_B002_6
               PUSH  DX
               MOV   DX,$03C8
               MOV   AL,$03
               OUT   DX,AL
               INC   DX
               MOV   AL,BYTE PTR EMULCOLORS[CS:(3*3)]
               OUT   DX,AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(3*3+1)]
               OUT   DX,AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(3*3+2)]
               OUT   DX,AL
               MOV   DX,$03C8
               MOV   AL,$07
               OUT   DX,AL
               INC   DX
               MOV   AL,BYTE PTR EMULCOLORS[CS:(7*3)]
               OUT   DX,AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(7*3+1)]
               OUT   DX,AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(7*3+2)]
               OUT   DX,AL
               POP   DX
               JMP   @S_B002_4
@S_B002_6:     PUSH  DX
               MOV   DX,$03C8
               MOV   AL,$01
               OUT   DX,AL
               INC   DX
               MOV   AL,BYTE PTR EMULCOLORS[CS:(1*3)]
               OUT   DX,AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(1*3+1)]
               OUT   DX,AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(1*3+2)]
               OUT   DX,AL
               MOV   DX,$03C8
               MOV   AL,$07
               OUT   DX,AL
               INC   DX
               MOV   AL,BYTE PTR EMULCOLORS[CS:(7*3)]
               OUT   DX,AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(7*3+1)]
               OUT   DX,AL
               MOV   AL,BYTE PTR EMULCOLORS[CS:(7*3+2)]
               OUT   DX,AL
               POP   DX
               JMP   @S_B002_4
@S_B002_5:     CMP   BYTE PTR [CS:GRAPHMODE],$05
               JB    @S_B002_7
               PUSH  DX
               MOV   DX,$03C8
               MOV   AL,$03
               OUT   DX,AL
               INC   DX
               MOV   AL,BYTE PTR INTENSCOLOR[CS:$00]
               OUT   DX,AL
               MOV   AL,BYTE PTR INTENSCOLOR[CS:$01]
               OUT   DX,AL
               MOV   AL,BYTE PTR INTENSCOLOR[CS:$02]
               OUT   DX,AL
               MOV   DX,$03C8
               MOV   AL,$07
               OUT   DX,AL
               INC   DX
               MOV   AL,BYTE PTR INTENSCOLOR[CS:$00]
               OUT   DX,AL
               MOV   AL,BYTE PTR INTENSCOLOR[CS:$01]
               OUT   DX,AL
               MOV   AL,BYTE PTR INTENSCOLOR[CS:$02]
               OUT   DX,AL
               POP   DX
               JMP   @S_B002_4
@S_B002_7:     PUSH  DX
               MOV   DX,$03C8
               MOV   AL,$01
               OUT   DX,AL
               INC   DX
               MOV   AL,BYTE PTR INTENSMONO[CS:$00]
               OUT   DX,AL
               MOV   AL,BYTE PTR INTENSMONO[CS:$01]
               OUT   DX,AL
               MOV   AL,BYTE PTR INTENSMONO[CS:$02]
               OUT   DX,AL
               CMP   BYTE PTR [CS:GRAPHMODE],$00
               JZ    @S_B002_9
               MOV   DX,$03C8
               MOV   AL,$07
               OUT   DX,AL
               INC   DX
               MOV   AL,BYTE PTR INTENSMONO[CS:$00]
               OUT   DX,AL
               MOV   AL,BYTE PTR INTENSMONO[CS:$01]
               OUT   DX,AL
               MOV   AL,BYTE PTR INTENSMONO[CS:$02]
               OUT   DX,AL
@S_B002_9:     POP   DX
@S_B002_4:     POP   AX
               AND   AX,$0404
               CMP   AL,AH
               JZ    @S_B002_2
               CMP   BYTE PTR [CS:SOUNDOUTPUT],$00
               JZ    @S_B002_2
               CMP   BYTE PTR @SBAVAIL,$00
               JNZ   @S_B002_3
               IN    AL,$61
               XOR   AL,$02
               OUT   $61,AL
               ADD   WORD PTR [PCCYCLES],+95
               JMP   @NEXTOPC
@S_B002_3:     CALL  SBSOUND
               ADD   WORD PTR [PCCYCLES],+300
               JMP   @NEXTOPC
@S_B002_2:     ADD   WORD PTR [PCCYCLES],+25
               JMP   @NEXTOPC

{---[sta/stx/sty/stz_b003]--------------------------------------------------}
@STZ_B003:     MOV   AL,$00
               JMP   @S_B003_1
@STA_B003:     MOV   AL,BL
               JMP   @S_B003_1
@STX_B003:     MOV   AL,CL
               JMP   @S_B003_1
@STY_B003:     MOV   AL,DL
@S_B003_1:     TEST  AL,00001000b
               JNZ   @S_B003_2
               PUSH  CX
               MOV   CL,AL
               AND   CL,00000110b
               SHR   CL,1
               AND   AL,00000001b
               SHL   AL,CL
               POP   CX
               MOV   AH,AL
               NEG   AH
               AND   AH,BYTE PTR [$B002]
               OR    AL,AH
               JMP   @S_B002_1
@S_B003_2:     ADD   WORD PTR [PCCYCLES],+10
               JMP   @NEXTOPC

{---[sta/stx/sty/stz_b000]--------------------------------------------------}
@STZ_B000:     MOV   AL,$00
               JMP   @S_B000_1
@STA_B000:     MOV   AL,BL
               JMP   @S_B000_1
@STX_B000:     MOV   AL,CL
               JMP   @S_B000_1
@STY_B000:     MOV   AL,DL
@S_B000_1:     ADD   WORD PTR [PCCYCLES],+25
               MOV   BYTE PTR [$B000],AL
               SHR   AL,5
               JNC   @S_B000_2 {lores}
               SHR   AL,1
               JNC   @S_B000_3 {hires color mode}
               INC   AL        {hires mode}
               JMP   @S_B000_4
@S_B000_3:     ADD   AL,$05
               JMP   @S_B000_4
@S_B000_2:     MOV   AL,$00
@S_B000_4:     CMP   AL,BYTE PTR [CS:GRAPHMODE]
               JZ    @S_B000_5
               MOV   BYTE PTR [CS:GRAPHMODE],AL
               CALL  SETBORDERCOL
               CALL  REBUILDSCREEN
@S_B000_5:     JMP   @NEXTOPC

{---[90h: bcc relative]-----------------------------------------------------}
@OPCODE90:     MOV   AL,BH
               SHR   AL,1 {get carry}
               JC    @OPC90_1
               MOV   WORD PTR [INSTRCYCLES],$1303
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CBW
               ADD   SI,AX
               JMP   @NEXTOPC
@OPC90_1:      MOV   WORD PTR [INSTRCYCLES],$0E02
               INC   SI
               JMP   @NEXTOPC

{---[91h: sta (indirect),y]-------------------------------------------------}
@OPCODE91:     MOV   WORD PTR [INSTRCYCLES],$2306
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   AX,WORD PTR [DI] {get address from atom memory}
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               JMP   @STORE_A

{---[92h: sta (indirect)]---------------------------------------------------}
@OPCODE92:     MOV   WORD PTR [INSTRCYCLES],$2405
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   AX,WORD PTR [DI] {get address from atom memory}
               JMP   @STORE_A

{---[94h: sty zero page,x]--------------------------------------------------}
@OPCODE94:     MOV   WORD PTR [INSTRCYCLES],$1004
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL
               MOV   AH,$00
               MOV   DI,AX
               MOV   BYTE PTR [DI],DL
               JMP   @NEXTOPC

{---[95h: sta zero page,x]--------------------------------------------------}
@OPCODE95:     MOV   WORD PTR [INSTRCYCLES],$1004
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL
               MOV   AH,$00
               MOV   DI,AX
               MOV   BYTE PTR [DI],BL
               JMP   @NEXTOPC

{---[96h: stx zero page,y]--------------------------------------------------}
@OPCODE96:     MOV   WORD PTR [INSTRCYCLES],$1004
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,DL
               MOV   AH,$00
               MOV   DI,AX
               MOV   BYTE PTR [DI],CL
               JMP   @NEXTOPC

{---[98h: tya implied]------------------------------------------------------}
@OPCODE98:     MOV   WORD PTR [INSTRCYCLES],$0902+$0F00
               MOV   BL,DL
               OR    BL,BL
               JMP   @UPDATENZ

{---[99h: sta absolute,y]---------------------------------------------------}
@OPCODE99:     MOV   WORD PTR [INSTRCYCLES],$2105
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               JMP   @STORE_A

{---[9Ah: txs implied]------------------------------------------------------}
@OPCODE9A:     MOV   WORD PTR [INSTRCYCLES],$0902
               MOV   AL,CL
               MOV   AH,$00
               MOV   BP,AX
               JMP   @NEXTOPC

{---[9Bh: txy implied]------------------------------------------------------}
@OPCODE9B:     MOV   WORD PTR [INSTRCYCLES],$0902+$0F00
               MOV   DL,CL
               OR    DL,DL
               JMP   @UPDATENZ

{---[9Ch: stz absolute]-----------------------------------------------------}
@OPCODE9C:     MOV   WORD PTR [INSTRCYCLES],$1F04
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
@STORE_Z:      MOV   DI,AX
               MOV   AL,AH
               AND   AL,$F0
               CMP   AL,$A0
               JB    @OPC9C_2
               CMP   AL,$B0
               JNZ   @OPC9C_3
               CMP   AH,$B0
               JNZ   @OPC9C_4
               CMP   DI,$B000
               JZ    @STZ_B000
               CMP   DI,$B002
               JZ    @STZ_B002
               CMP   DI,$B003
               JNZ   @OPC9C_3
               JMP   @STZ_B003
@OPC9C_4:      CMP   AH,$B8
               JZ    @STZ_VIA
               JB    @OPC9C_5
               CMP   AH,$BA
               JNZ   @OPC9C_6
               MOV   AL,$00
               CALL  WRITE_FDC
               JMP   @NEXTOPC
@OPC9C_6:      CMP   DI,$BFE0
               JZ    @STZ_MOUSEX
               CMP   DI,$BFE1
               JZ    @STZ_MOUSEY
               CMP   DI,$BFE2
               JNZ   @OPC9C_1
               MOV   AL,$00
               JMP   @STORE_MOUSENR
@OPC9C_1:      CMP   DI,SCHAKELBYTE
               JNZ   @OPC9C_3
               CALL  SAVEZP90
               MOV   BYTE PTR [DI],$00
               CALL  SETA000MEM
               JMP   @NEXTOPC
@OPC9C_2:      MOV   BYTE PTR [DI],$00
               CALL  UPDATEGRAPH
@OPC9C_3:      JMP   @NEXTOPC
@OPC9C_5:      CMP   AH,$B4
               JB    @OPC9C_3
               MOV   AL,$00
               PUSH  DX
               MOV   DX,DI
               AND   DX,$03FF
               OUT   DX,AL
               POP   DX
               JMP   @NEXTOPC

{---[9Dh: sta absolute,x]---------------------------------------------------}
@OPCODE9D:     MOV   WORD PTR [INSTRCYCLES],$2105
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               JMP   @STORE_A

{---[9Eh: stz absolute,x]---------------------------------------------------}
@OPCODE9E:     MOV   WORD PTR [INSTRCYCLES],$2105
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               JMP   @STORE_Z

{---[A0h: ldy immediate]----------------------------------------------------}
@OPCODEA0:     MOV   WORD PTR [INSTRCYCLES],$0B02+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   DL,AL
               OR    AL,AL
               JMP   @UPDATENZ

{---[A1h: lda (indirect,x)]-------------------------------------------------}
@OPCODEA1:     MOV   WORD PTR [INSTRCYCLES],$1D06+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   DI,WORD PTR [DI] {get address from atom memory}
               JMP   @LOAD_A

{---[A2h: ldx immediate]----------------------------------------------------}
@OPCODEA2:     MOV   WORD PTR [INSTRCYCLES],$0B02+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   CL,AL
               OR    AL,AL
               JMP   @UPDATENZ

{---[A4h: ldy zero page]----------------------------------------------------}
@OPCODEA4:     MOV   WORD PTR [INSTRCYCLES],$1003+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   DL,BYTE PTR [DI]
               OR    DL,DL
               JMP   @UPDATENZ

{---[A5h: lda zero page]----------------------------------------------------}
@OPCODEA5:     MOV   WORD PTR [INSTRCYCLES],$1003+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   BL,BYTE PTR [DI]
               OR    BL,BL
               JMP   @UPDATENZ

{---[A6h: ldx zero page]----------------------------------------------------}
@OPCODEA6:     MOV   WORD PTR [INSTRCYCLES],$1003+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   CL,BYTE PTR [DI]
               OR    CL,CL
               JMP   @UPDATENZ

{---[A8h: tay implied]------------------------------------------------------}
@OPCODEA8:     MOV   WORD PTR [INSTRCYCLES],$0902+$0F00
               MOV   DL,BL
               OR    DL,DL
               JMP   @UPDATENZ

{---[A9h: lda immediate]----------------------------------------------------}
@OPCODEA9:     MOV   WORD PTR [INSTRCYCLES],$0B02+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   BL,AL
               OR    AL,AL
               JMP   @UPDATENZ

{---[AAh: tax implied]------------------------------------------------------}
@OPCODEAA:     MOV   WORD PTR [INSTRCYCLES],$0902+$0F00
               MOV   CL,BL
               OR    CL,CL
               JMP   @UPDATENZ

{---[lda/ldx/ldy_b002]------------------------------------------------------}
@LDY_B002:     CALL  @L_B002_1
               MOV   DL,AL
               JMP   @UPDATENZ
@LDA_B002:     CALL  @L_B002_1
               MOV   BL,AL
               JMP   @UPDATENZ
@LDX_B002:     CALL  @L_B002_1
               MOV   CL,AL
               JMP   @UPDATENZ
@L_B002_1:     TEST  BYTE PTR [CS:CPUSPEEDMODE],$01
               JZ    @L_B002_4
               MOV   AL,$00
               CMP   WORD PTR [AANTCYCLES],CYCLESFLYBACK
               JB    @L_B002_6
               MOV   AL,$80
               CMP   WORD PTR [AANTCYCLES],(1026620/60)
               JB    @L_B002_6
               JMP   @L_B002_7
@L_B002_4:     MOV   AL,$00
               CMP   WORD PTR [AANTCYCLES],CYCLESFLYBACK
               JB    @L_B002_6
               CMP   WORD PTR [AANTCYCLES],(1026620/60)
               JAE   @L_B002_5
               PUSH  DX
               MOV   DX,$03DA
               IN    AL,DX
               POP   DX
               TEST  AL,$08
               JNZ   @L_B002_7
               MOV   AL,$80
               JMP   @L_B002_6
@L_B002_5:     PUSH  BX
               MOV   BX,$0A00
               PUSH  DX
               MOV   DX,$03DA
@L_B002_9:     IN    AL,DX
               TEST  AL,$08
               JNZ   @L_B002_10
               DEC   BX
               JNZ   @L_B002_9
@L_B002_10:    POP   DX
               POP   BX
@L_B002_7:     MOV   WORD PTR [AANTCYCLES],$0000
               MOV   AL,$00
@L_B002_6:     AND   BYTE PTR [$B002],$7F
               OR    AL,BYTE PTR [$B002]
@L_B002_3:     PUSH  DI
               MOV   DI,$0038 {---alt---}
               CMP   BYTE PTR [CS:ALTKEYB],$00
               JZ    @L_B002_8
               MOV   DI,$0036 {---right shift---}
@L_B002_8:     TEST  BYTE PTR TOETS[CS:DI],$03
               POP   DI
               JZ    @L_B002_2
               ADD   WORD PTR [PCCYCLES],+158
               AND   AL,$BF
               RETN
@L_B002_2:     ADD   WORD PTR [PCCYCLES],+158
               OR    AL,$40
               RETN

{---[lda/ldx/ldy_b003]------------------------------------------------------}
@LDY_B003:     CALL  @L_B003_1
               MOV   DL,AL
               JMP   @UPDATENZ
@LDA_B003:     CALL  @L_B003_1
               MOV   BL,AL
               JMP   @UPDATENZ
@LDX_B003:     CALL  @L_B003_1
               MOV   CL,AL
               JMP   @UPDATENZ
@L_B003_1:     AND   BYTE PTR [$B003],$3F
               MOV   AL,$C0
               OR    AL,BYTE PTR [$B003]
               CMP   BYTE PTR [CS:ALTKEYB],$00
               JNZ   @L_B003_9
               {---standard keyboard---}
               MOV   AH,BYTE PTR TOETS[CS:$2A] {---left shift---}
               OR    AH,BYTE PTR TOETS[CS:$36] {---right shift---}
               OR    AH,BYTE PTR TOETS[CS:$4B] {---crsr left---}
               OR    AH,BYTE PTR TOETS[CS:$50] {---crsr down---}
               AND   AH,$03
               JZ    @L_B003_5
               AND   AL,$7F
@L_B003_5:     MOV   AH,BYTE PTR TOETS[CS:$1D] {---ctrl---}
               OR    AH,BYTE PTR TOETS[CS:$38] {---alt---}
               AND   AH,$03
               JZ    @L_B003_3
               AND   AL,$BF
               JMP   @L_B003_3
@L_B003_9:     {---alternate keyboard---}
               MOV   AH,BYTE PTR TOETS[CS:$1D] {---ctrl---}
               OR    AH,BYTE PTR TOETS[CS:$38] {---alt---}
               AND   AH,$03
               JZ    @L_B003_10
               AND   AL,$7F
@L_B003_10:    MOV   AH,BYTE PTR TOETS[CS:$2A] {---left shift---}
               OR    AH,BYTE PTR TOETS[CS:$36] {---right shift---}
               AND   AH,$03
               JZ    @L_B003_3
               AND   AL,$BF
@L_B003_3:     ADD   WORD PTR [PCCYCLES],+158
               OR    AL,AL
               RETN

{---[ACh: ldy absolute]-----------------------------------------------------}
@OPCODEAC:     MOV   WORD PTR [INSTRCYCLES],$1604+$0F00
               MOV   DI,WORD PTR [SI]
               ADD   SI,+$02
@LOAD_Y:       CMP   DI,$B001
               JB    @OPCAC_1
               JZ    @LDY_B001
               CMP   DI,$B003
               JB    @LDY_B002
               JZ    @LDY_B003
               MOV   AX,DI
               CMP   AH,$B8
               JZ    @LDY_VIA
               JB    @OPCAC_3
               CMP   AH,$BA
               JNZ   @OPCAC_2
               CALL  READ_FDC
               MOV   DL,AL
               OR    AL,AL
               JMP   @UPDATENZ
@OPCAC_2:      CMP   AX,FLIPFLOP
               JNZ   @OPCAC_1
               NOT   BYTE PTR [DI]
@OPCAC_1:      MOV   DL,BYTE PTR [DI]
               OR    DL,DL
               JMP   @UPDATENZ
@OPCAC_3:      CMP   AH,$B4
               JB    @OPCAC_2
               PUSH  DX
               AND   AX,$03FF
               MOV   DX,AX
               IN    AL,DX
               MOV   BYTE PTR [DI],AL
               POP   DX
               MOV   DL,AL
               OR    DL,DL
               JMP   @UPDATENZ


{---[ADh: lda absolute]-----------------------------------------------------}
@OPCODEAD:     MOV   WORD PTR [INSTRCYCLES],$1604+$0F00
               MOV   DI,WORD PTR [SI]
               ADD   SI,+$02
@LOAD_A:       CMP   DI,$B001
               JB    @OPCAD_1
               JZ    @LDA_B001
               CMP   DI,$B003
               JB    @LDA_B002
               JZ    @LDA_B003
               MOV   AX,DI
               CMP   AH,$B8
               JZ    @LDA_VIA
               JB    @OPCAD_3
               CMP   AH,$BA
               JNZ   @OPCAD_2
               CALL  READ_FDC
               MOV   BL,AL
               OR    AL,AL
               JMP   @UPDATENZ
@OPCAD_2:      CMP   AX,FLIPFLOP
               JNZ   @OPCAD_1
               NOT   BYTE PTR [DI]
@OPCAD_1:      MOV   BL,BYTE PTR [DI]
               OR    BL,BL
               JMP   @UPDATENZ
@OPCAD_3:      CMP   AH,$B4
               JB    @OPCAD_2
               PUSH  DX
               AND   AX,$03FF
               MOV   DX,AX
               IN    AL,DX
               MOV   BYTE PTR [DI],AL
               POP   DX
               MOV   BL,AL
               OR    BL,BL
               JMP   @UPDATENZ

{---[AEh: ldx absolute]-----------------------------------------------------}
@OPCODEAE:     MOV   WORD PTR [INSTRCYCLES],$1604+$0F00
               MOV   DI,WORD PTR [SI]
               ADD   SI,+$02
@LOAD_X:       CMP   DI,$B001
               JB    @OPCAE_1
               JZ    @LDX_B001
               CMP   DI,$B003
               JB    @LDX_B002
               JZ    @LDX_B003
               MOV   AX,DI
               CMP   AH,$B8
               JZ    @LDX_VIA
               JB    @OPCAE_3
               CMP   AH,$BA
               JNZ   @OPCAE_2
               CALL  READ_FDC
               MOV   CL,AL
               OR    AL,AL
               JMP   @UPDATENZ
@OPCAE_2:      CMP   AX,FLIPFLOP
               JNZ   @OPCAE_1
               NOT   BYTE PTR [DI]
@OPCAE_1:      MOV   CL,BYTE PTR [DI]
               OR    CL,CL
               JMP   @UPDATENZ
@OPCAE_3:      CMP   AH,$B4
               JB    @OPCAE_2
               PUSH  DX
               AND   AX,$03FF
               MOV   DX,AX
               IN    AL,DX
               MOV   BYTE PTR [DI],AL
               POP   DX
               MOV   CL,AL
               OR    CL,CL
               JMP   @UPDATENZ

{---[lda/ldx/ldy_b001]------------------------------------------------------}
@LDY_B001:     CALL  @L_B001_1
               MOV   DL,AL
               OR    AL,AL
               JMP   @UPDATENZ
@LDA_B001:     CALL  @L_B001_1
               MOV   BL,AL
               OR    AL,AL
               JMP   @UPDATENZ
@LDX_B001:     CALL  @L_B001_1
               MOV   CL,AL
               OR    AL,AL
               JMP   @UPDATENZ
@L_B001_1:     MOV   AL,$FF
               CMP   BYTE PTR [CS:ALTKEYB],$00
               JNZ   @L_B001_9
               {---standard keyboard---}
               MOV   AH,BYTE PTR TOETS[CS:$2A] {---left shift---}
               OR    AH,BYTE PTR TOETS[CS:$36] {---right shift---}
               OR    AH,BYTE PTR TOETS[CS:$4B] {---crsr left---}
               OR    AH,BYTE PTR TOETS[CS:$50] {---crsr down---}
               AND   AH,$03
               JZ    @L_B001_5
               AND   AL,$7F
@L_B001_5:     TEST  BYTE PTR TOETS[CS:$1D],$03 {---ctrl---}
               JZ    @L_B001_3
               AND   AL,$BF
               JMP   @L_B001_3
@L_B001_9:     {---alternate keyboard---}
               MOV   AH,BYTE PTR TOETS[CS:$1D] {---ctrl---}
               OR    AH,BYTE PTR TOETS[CS:$38] {---alt---}
               AND   AH,$03
               JZ    @L_B001_10
               AND   AL,$7F
@L_B001_10:    TEST  BYTE PTR TOETS[CS:$2A],$03 {---left shift---}
               JZ    @L_B001_3
               AND   AL,$BF
@L_B001_3:     PUSH  BX
               MOV   BL,BYTE PTR [$B000]
               AND   BX,$000F
               CMP   BL,$09
               JA    @L_B001_6
               SHL   BX,3
               MOV   DI,BX
               CMP   BYTE PTR [CS:ALTKEYB],$00
               JNZ   @L_B001_8
               ADD   DI,OFFSET KEYSCAN
               JMP   @L_B001_7
@L_B001_8:     ADD   DI,OFFSET ALTKEYSCAN
@L_B001_7:     MOV   AH,11111110b
@L_B001_4:     MOV   BL,BYTE PTR [CS:DI]
               TEST  BYTE PTR TOETS[CS:BX],$03 {BH=0}
               JZ    @L_B001_2
               AND   AL,AH
@L_B001_2:     INC   DI
               STC
               RCL   AH,1
               CMP   AH,10111111b
               JNZ   @L_B001_4
@L_B001_6:     POP   BX
               MOV   BYTE PTR [$B001],AL
               ADD   WORD PTR [PCCYCLES],+156
               RETN

{---[B0h: bcs relative]-----------------------------------------------------}
@OPCODEB0:     MOV   AL,BH
               SHR   AL,1 {get carry}
               JNC   @OPCB0_1
               MOV   WORD PTR [INSTRCYCLES],$1303
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CBW
               ADD   SI,AX
               JMP   @NEXTOPC
@OPCB0_1:      MOV   WORD PTR [INSTRCYCLES],$0E02
               INC   SI
               JMP   @NEXTOPC

{---[B1h: lda (indirect),y]-------------------------------------------------}
@OPCODEB1:     MOV   WORD PTR [INSTRCYCLES],$1E05+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   AX,WORD PTR [DI] {get address from atom memory}
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               MOV   DI,AX
               JMP   @LOAD_A

{---[B2h: lda (indirect)]---------------------------------------------------}
@OPCODEB2:     MOV   WORD PTR [INSTRCYCLES],$1C05+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   DI,WORD PTR [DI] {get address from atom memory}
               JMP   @LOAD_A

{---[B4h: ldy zero page,x]--------------------------------------------------}
@OPCODEB4:     MOV   WORD PTR [INSTRCYCLES],$1104+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   DL,BYTE PTR [DI]
               OR    DL,DL
               JMP   @UPDATENZ

{---[B5h: lda zero page,x]--------------------------------------------------}
@OPCODEB5:     MOV   WORD PTR [INSTRCYCLES],$1104+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   BL,BYTE PTR [DI]
               OR    BL,BL
               JMP   @UPDATENZ

{---[B6h: ldx zero page,y]--------------------------------------------------}
@OPCODEB6:     MOV   WORD PTR [INSTRCYCLES],$1104+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,DL {add y-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   CL,BYTE PTR [DI]
               OR    CL,CL
               JMP   @UPDATENZ

{---[B8h: clv]--------------------------------------------------------------}
@OPCODEB8:     MOV   WORD PTR [INSTRCYCLES],$0802
               AND   BH,10111111b
               JMP   @NEXTOPC

{---[B9h: lda absolute,y]---------------------------------------------------}
@OPCODEB9:     MOV   WORD PTR [INSTRCYCLES],$1B04+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               MOV   DI,AX
               JMP   @LOAD_A

{---[BAh: tsx implied]------------------------------------------------------}
@OPCODEBA:     MOV   WORD PTR [INSTRCYCLES],$0902+$0F00
               MOV   AX,BP
               MOV   CL,AL
               OR    AL,AL
               JMP   @UPDATENZ

{---[BBh: tyx implied]------------------------------------------------------}
@OPCODEBB:     MOV   WORD PTR [INSTRCYCLES],$0902+$0F00
               MOV   CL,DL
               OR    CL,CL
               JMP   @UPDATENZ

{---[BCh: ldy absolute,x]---------------------------------------------------}
@OPCODEBC:     MOV   WORD PTR [INSTRCYCLES],$1B04+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               MOV   DI,AX
               JMP   @LOAD_Y

{---[BDh: lda absolute,x]---------------------------------------------------}
@OPCODEBD:     MOV   WORD PTR [INSTRCYCLES],$1B04+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               MOV   DI,AX
               JMP   @LOAD_A

{---[BEh: ldx absolute,y]---------------------------------------------------}
@OPCODEBE:     MOV   WORD PTR [INSTRCYCLES],$1B04+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               MOV   DI,AX
               JMP   @LOAD_X

{---[C0h: cpy immediate]----------------------------------------------------}
@OPCODEC0:     MOV   WORD PTR [INSTRCYCLES],$0D02+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CMP   DL,AL
               CMC
               JMP   @UPDATECNZ

{---[C1h: cmp (indirect,x)]-------------------------------------------------}
@OPCODEC1:     MOV   WORD PTR [INSTRCYCLES],$1606+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   DI,WORD PTR [DI] {get address from atom memory}
               CMP   BL,BYTE PTR [DI]
               CMC
               JMP   @UPDATECNZ

{---[C4h: cpy zero page]----------------------------------------------------}
@OPCODEC4:     MOV   WORD PTR [INSTRCYCLES],$1203+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               CMP   DL,BYTE PTR [DI]
               CMC
               JMP   @UPDATECNZ

{---[C5h: cmp zero page]----------------------------------------------------}
@OPCODEC5:     MOV   WORD PTR [INSTRCYCLES],$1203+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               CMP   BL,BYTE PTR [DI]
               CMC
               JMP   @UPDATECNZ

{---[C6h: dec zero page]----------------------------------------------------}
@OPCODEC6:     MOV   WORD PTR [INSTRCYCLES],$1105+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               DEC   BYTE PTR [DI]
               JMP   @UPDATENZ

{---[C8h: iny implied]------------------------------------------------------}
@OPCODEC8:     MOV   WORD PTR [INSTRCYCLES],$0802+$0F00
               INC   DL
               JMP   @UPDATENZ

{---[C9h: cmp immediate]----------------------------------------------------}
@OPCODEC9:     MOV   WORD PTR [INSTRCYCLES],$0D02+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CMP   BL,AL
               CMC
               JMP   @UPDATECNZ

{---[CAh: dex implied]------------------------------------------------------}
@OPCODECA:     MOV   WORD PTR [INSTRCYCLES],$0802+$0F00
               DEC   CL
               JMP   @UPDATENZ

{---[CCh: cpy absolute]-----------------------------------------------------}
@OPCODECC:     MOV   WORD PTR [INSTRCYCLES],$1004+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               MOV   DI,AX
               CMP   DL,BYTE PTR [DI]
               CMC
               JMP   @UPDATECNZ

{---[CDh: cmp absolute]-----------------------------------------------------}
@OPCODECD:     MOV   WORD PTR [INSTRCYCLES],$1204+$0F00
               MOV   DI,WORD PTR [SI]
               ADD   SI,+$02
               CMP   DI,FLIPFLOP
               JNZ   @OPCCD_1
               NOT   BYTE PTR [DI]
@OPCCD_1:      CMP   BL,BYTE PTR [DI]
               CMC
               JMP   @UPDATECNZ

{---[CEh: dec absolute]-----------------------------------------------------}
@OPCODECE:     MOV   WORD PTR [INSTRCYCLES],$1406+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
@DEC_ABS:      MOV   DI,AX
               AND   AH,$F0
               CMP   AH,$A0
               JAE   @OPCCE_1
               DEC   BYTE PTR [DI]
               CALL  UPDATEGRAPH
               JMP   @UPDATENZ
@OPCCE_1:      CMP   AH,$B0
               JZ    @OPCCE_2
               MOV   AL,BYTE PTR [DI]
               DEC   AL
               JMP   @UPDATENZ
@OPCCE_2:      CMP   DI,$B002
               JNZ   @OPCCE_3
               MOV   AH,AL
               AND   AH,$F0
               DEC   AL
               AND   AL,$0F
               OR    AL,AH
               MOV   BYTE PTR [$B002],AL
               JMP   @UPDATENZ
@OPCCE_3:      CMP   DI,SCHAKELBYTE
               JZ    @OPCCE_4
               DEC   BYTE PTR [DI]
               JMP   @UPDATENZ
@OPCCE_4:      CALL  SAVEZP90
               DEC   BYTE PTR [DI]
               PUSHF
               CALL  SETA000MEM
               POPF
               JMP   @UPDATENZ

{---[D0h: bne relative]-----------------------------------------------------}
@OPCODED0:     MOV   AL,BH
               SHR   AL,2 {get zero}
               JC    @OPCD0_1
               MOV   WORD PTR [INSTRCYCLES],$1303
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CBW
               ADD   SI,AX
               JMP   @NEXTOPC
@OPCD0_1:      MOV   WORD PTR [INSTRCYCLES],$0E02
               INC   SI
               JMP   @NEXTOPC

{---[D1h: cmp (indirect),y]-------------------------------------------------}
@OPCODED1:     MOV   WORD PTR [INSTRCYCLES],$1905+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   AX,WORD PTR [DI] {get address from atom memory}
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               MOV   DI,AX
               CMP   BL,BYTE PTR [DI]
               CMC
               JMP   @UPDATECNZ

{---[D2h: cmp (indirect)]---------------------------------------------------}
@OPCODED2:     MOV   WORD PTR [INSTRCYCLES],$1505+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   DI,WORD PTR [DI] {get address from atom memory}
               CMP   BL,BYTE PTR [DI]
               CMC
               JMP   @UPDATECNZ

{---[D5h: cmp zero page,x]--------------------------------------------------}
@OPCODED5:     MOV   WORD PTR [INSTRCYCLES],$1304+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               CMP   BL,BYTE PTR [DI]
               CMC
               JMP   @UPDATECNZ

{---[D6h: dec zero page,x]--------------------------------------------------}
@OPCODED6:     MOV   WORD PTR [INSTRCYCLES],$1206+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               DEC   BYTE PTR [DI]
               JMP   @UPDATENZ

{---[D8h: cld]--------------------------------------------------------------}
@OPCODED8:     MOV   WORD PTR [INSTRCYCLES],$0802
               AND   BH,11110111b
               JMP   @NEXTOPC

{---[D9h: cmp absolute,y]---------------------------------------------------}
@OPCODED9:     MOV   WORD PTR [INSTRCYCLES],$1304+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               MOV   DI,AX
               CMP   BL,BYTE PTR [DI]
               CMC
               JMP   @UPDATECNZ

{---[DAh: phx implied]------------------------------------------------------}
@OPCODEDA:     MOV   WORD PTR [INSTRCYCLES],$0903
               AND   BP,$00FF
               MOV   BYTE PTR [DS:BP+STACKBASE],CL
               DEC   BP
               JMP   @NEXTOPC

{---[DDh: cmp absolute,x]---------------------------------------------------}
@OPCODEDD:     MOV   WORD PTR [INSTRCYCLES],$1304+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               MOV   DI,AX
               CMP   BL,BYTE PTR [DI]
               CMC
               JMP   @UPDATECNZ

{---[DEh: dec absolute,x]---------------------------------------------------}
@OPCODEDE:     MOV   WORD PTR [INSTRCYCLES],$1607+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               JMP   @DEC_ABS

{---[E0h: cpx immediate]----------------------------------------------------}
@OPCODEE0:     MOV   WORD PTR [INSTRCYCLES],$0D02+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CMP   CL,AL
               CMC
               JMP   @UPDATECNZ

{---[E1h: sbc (indirect,x)]-------------------------------------------------}
@OPCODEE1:     MOV   WORD PTR [INSTRCYCLES],$2006+$1400
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   DI,WORD PTR [DI] {get address from atom memory}
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @SBC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               CMC
               SBB   BL,AL
               CMC
               JMP   @UPDATECVNZ

{---[E4h: cpx zero page]----------------------------------------------------}
@OPCODEE4:     MOV   WORD PTR [INSTRCYCLES],$1203+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               CMP   CL,BYTE PTR [DI]
               CMC
               JMP   @UPDATECNZ

{---[E5h: sbc zero page]----------------------------------------------------}
@OPCODEE5:     MOV   WORD PTR [INSTRCYCLES],$1C03+$1400
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @SBC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               CMC
               SBB   BL,AL
               CMC
               JMP   @UPDATECVNZ

{---[E6h: inc zero page]----------------------------------------------------}
@OPCODEE6:     MOV   WORD PTR [INSTRCYCLES],$1105+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               INC   BYTE PTR [DI]
               JMP   @UPDATENZ

{---[E8h: inx implied]------------------------------------------------------}
@OPCODEE8:     MOV   WORD PTR [INSTRCYCLES],$0802+$0F00
               INC   CL
               JMP   @UPDATENZ

{---[E9h: sbc immediate]----------------------------------------------------}
@OPCODEE9:
               MOV   WORD PTR [INSTRCYCLES],$1702+$1400
               MOV   AL,BYTE PTR [SI]
               INC   SI
               TEST  BH,00001000b
               JNZ   @SBC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               CMC
               SBB   BL,AL
               CMC
               JMP   @UPDATECVNZ

{---[EAh: nop implied]------------------------------------------------------}
@OPCODEEA:
@OPCODE03:
@OPCODE07:
@OPCODE0B:
@OPCODE0F:
@OPCODE13:
@OPCODE17:
@OPCODE1F:
@OPCODE23:
@OPCODE27:
@OPCODE2B:
@OPCODE2F:
@OPCODE33:
@OPCODE37:
@OPCODE3F:
@OPCODE43:
@OPCODE47:
@OPCODE4B:
@OPCODE4F:
@OPCODE53:
@OPCODE57:
@OPCODE5B:
@OPCODE5F:
@OPCODE63:
@OPCODE67:
@OPCODE6B:
@OPCODE6F:
@OPCODE73:
@OPCODE77:
@OPCODE7B:
@OPCODE7F:
@OPCODE83:
@OPCODE87:
@OPCODE8B:
@OPCODE8F:
@OPCODE93:
@OPCODE97:
@OPCODE9F:
@OPCODEA3:
@OPCODEA7:
@OPCODEAB:
@OPCODEAF:
@OPCODEB3:
@OPCODEB7:
@OPCODEBF:
@OPCODEC3:
@OPCODEC7:
@OPCODECB:
@OPCODECF:
@OPCODED3:
@OPCODED7:
@OPCODEDB:
@OPCODEDF:
@OPCODEE3:
@OPCODEE7:
@OPCODEEF:
@OPCODEF3:
@OPCODEF7:
@OPCODEFB:
@OPCODEFF:     MOV   WORD PTR [INSTRCYCLES],$0702
               JMP   @NEXTOPC

{---[EBh: swa implied]------------------------------------------------------}
@OPCODEEB:     MOV   WORD PTR [INSTRCYCLES],$0902+$0F00
               XCHG  BL,BYTE PTR [CS:ACCU_B]
               OR    BL,BL
               JMP   @UPDATENZ

{---[ECh: cpx absolute]-----------------------------------------------------}
@OPCODEEC:     MOV   WORD PTR [INSTRCYCLES],$1004+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               MOV   DI,AX
               CMP   CL,BYTE PTR [DI]
               CMC
               JMP   @UPDATECNZ

{---[EDh: sbc absolute]-----------------------------------------------------}
@OPCODEED:     MOV   WORD PTR [INSTRCYCLES],$1A04+$1400
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               MOV   DI,AX
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @SBC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               CMC
               SBB   BL,AL
               CMC
               JMP   @UPDATECVNZ

{---[EEh: inc absolute]-----------------------------------------------------}
@OPCODEEE:     MOV   WORD PTR [INSTRCYCLES],$1406+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
@INC_ABS:      MOV   DI,AX
               AND   AH,$F0
               CMP   AH,$A0
               JAE   @OPCEE_1
               INC   BYTE PTR [DI]
               CALL  UPDATEGRAPH
               JMP   @UPDATENZ
@OPCEE_1:      CMP   AH,$B0
               JZ    @OPCEE_2
               MOV   AL,BYTE PTR [DI]
               INC   AL
               JMP   @UPDATENZ
@OPCEE_2:      CMP   DI,$B002
               JNZ   @OPCEE_3
               MOV   AH,AL
               AND   AH,$F0
               INC   AL
               AND   AL,$0F
               OR    AL,AH
               MOV   BYTE PTR [$B002],AL
               JMP   @UPDATENZ
@OPCEE_3:      CMP   DI,SCHAKELBYTE
               JZ    @OPCEE_4
               INC   BYTE PTR [DI]
               JMP   @UPDATENZ
@OPCEE_4:      CALL  SAVEZP90
               INC   BYTE PTR [DI]
               PUSHF
               CALL  SETA000MEM
               POPF
               JMP   @UPDATENZ

{---[sbc_dec]---------------------------------------------------------------}
@SBC_DEC:      XCHG  AL,BL
               MOV   AH,BH
               SHR   AH,1 {get carry}
               CMC
               SBB   AL,BL
               JO    @SBCDEC1
               DAS
               CMC
               LAHF
               MOV   BL,AL
               AND   BH,10111111b {clear overflow}
               SAHF
               JMP   @UPDATECNZ
@SBCDEC1:      DAS
               CMC
               LAHF
               MOV   BL,AL
               OR    BH,01000000b {set overflow}
               SAHF
               JMP   @UPDATECNZ

{---[F0h: beq relative]-----------------------------------------------------}
@OPCODEF0:     MOV   AL,BH
               SHR   AL,2 {get zero}
               JNC   @OPCF0_1
               MOV   WORD PTR [INSTRCYCLES],$1303
               MOV   AL,BYTE PTR [SI]
               INC   SI
               CBW
               ADD   SI,AX
               JMP   @NEXTOPC
@OPCF0_1:      MOV   WORD PTR [INSTRCYCLES],$0E02
               INC   SI
               JMP   @NEXTOPC

{---[F1h: sbc (indirect),y]-------------------------------------------------}
@OPCODEF1:     MOV   WORD PTR [INSTRCYCLES],$2305+$1400
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   AX,WORD PTR [DI] {get address from atom memory}
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               MOV   DI,AX
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @SBC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               CMC
               SBB   BL,AL
               CMC
               JMP   @UPDATECVNZ

{---[F2h: sbc (indirect)]---------------------------------------------------}
@OPCODEF2:     MOV   WORD PTR [INSTRCYCLES],$1F05+$1400
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               MOV   DI,AX
               MOV   DI,WORD PTR [DI] {get address from atom memory}
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @SBC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               CMC
               SBB   BL,AL
               CMC
               JMP   @UPDATECVNZ

{---[F5h: sbc zero page,x]--------------------------------------------------}
@OPCODEF5:     MOV   WORD PTR [INSTRCYCLES],$1D04+$1400
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @SBC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               CMC
               SBB   BL,AL
               CMC
               JMP   @UPDATECVNZ

{---[F6h: inc zero page,x]--------------------------------------------------}
@OPCODEF6:     MOV   WORD PTR [INSTRCYCLES],$1206+$0F00
               MOV   AL,BYTE PTR [SI]
               INC   SI
               ADD   AL,CL {add x-reg}
               MOV   AH,$00
               MOV   DI,AX
               INC   BYTE PTR [DI]
               JMP   @UPDATENZ

{---[F8h: sed]--------------------------------------------------------------}
@OPCODEF8:     MOV   WORD PTR [INSTRCYCLES],$0802
               OR    BH,00001000b
               JMP   @NEXTOPC

{---[F9h: sbc absolute,y]---------------------------------------------------}
@OPCODEF9:     MOV   WORD PTR [INSTRCYCLES],$1D04+$1400
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,DL {add y-reg}
               ADC   AH,$00
               MOV   DI,AX
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @SBC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               CMC
               SBB   BL,AL
               CMC
               JMP   @UPDATECVNZ

{---[FAh: plx implied]------------------------------------------------------}
@OPCODEFA:     MOV   WORD PTR [INSTRCYCLES],$0904+$0F00
               INC   BP
               AND   BP,$00FF
               MOV   CL,BYTE PTR [DS:BP+STACKBASE]
               OR    CL,CL
               JMP   @UPDATENZ

{---[FCh: jsr (absolute,x)]-------------------------------------------------}
@OPCODEFC:     MOV   WORD PTR [INSTRCYCLES],$1906
               MOV   AX,SI
               INC   AX
               AND   BP,$00FF
               MOV   BYTE PTR [DS:BP+STACKBASE],AH
               DEC   BP
               AND   BP,$00FF
               MOV   BYTE PTR [DS:BP+STACKBASE],AL
               DEC   BP
               MOV   AX,WORD PTR [SI]
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               MOV   SI,AX
               MOV   SI,WORD PTR [SI]
               JMP   @NEXTOPC

{---[FDh: sbc absolute,x]---------------------------------------------------}
@OPCODEFD:     MOV   WORD PTR [INSTRCYCLES],$1D04+$1400
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               MOV   DI,AX
               MOV   AL,BYTE PTR [DI] {get byte from atom memory}
               TEST  BH,00001000b
               JNZ   @SBC_DEC
               MOV   AH,BH
               SHR   AH,1 {get carry}
               CMC
               SBB   BL,AL
               CMC
               JMP   @UPDATECVNZ

{---[FEh: inc absolute,x]---------------------------------------------------}
@OPCODEFE:     MOV   WORD PTR [INSTRCYCLES],$1607+$0F00
               MOV   AX,WORD PTR [SI]
               ADD   SI,+$02
               ADD   AL,CL {add x-reg}
               ADC   AH,$00
               JMP   @INC_ABS

{---[updatenz]--------------------------------------------------------------}
@UPDATENZ:     LAHF
               AND   BH,01111101b
               MOV   AL,AH
               AND   AH,10000000b
               OR    BH,AH {negative}
               AND   AL,01000000b
               SHR   AL,5
               OR    BH,AL {zero}
               JMP   @NEXTOPC

{---[updatecnz]-------------------------------------------------------------}
@UPDATECNZ:    LAHF
               AND   BH,01111100b
               MOV   AL,AH
               AND   AH,10000001b
               OR    BH,AH {negative & carry}
               AND   AL,01000000b
               SHR   AL,5
               OR    BH,AL {zero}
               JMP   @NEXTOPC

{---[updatecvnz]------------------------------------------------------------}
@UPDATECVNZ:   LAHF
               JNO   @CVNZ_2
               OR    BH,01000000b {overflow}
               JMP   @CVNZ_1
@CVNZ_2:       AND   BH,10111111b {no overflow}
@CVNZ_1:       AND   BH,01111100b
               MOV   AL,AH
               AND   AH,10000001b
               OR    BH,AH {negative & carry}
               AND   AL,01000000b
               SHR   AL,5
               OR    BH,AL {zero}
              {JMP   @NEXTOPC}

{---[nextopc]---------------------------------------------------------------}
@NEXTOPC:      MOV   AL,BYTE PTR [INSTRCYCLES]
               MOV   AH,$00
               TEST  BYTE PTR [$B80B],00100000b
               JNZ   @DECRTIM5
               {---t2 one shot mode---}
               SUB   WORD PTR [$B808],AX
               JA    @DECRTIM5
               TEST  BYTE PTR [$B80D],00100000b
               JNZ   @DECRTIM5
               OR    BYTE PTR [$B80D],00100000b
               TEST  BYTE PTR [$B80E],00100000b
               JZ    @DECRTIM5
               OR    BYTE PTR [IRQ_NMI],$02
               JMP   @DECRTIM2
@DECRTIM5:     TEST  BYTE PTR [$B80B],01000000b
               JNZ   @DECRTIM1
               {---t1 one shot mode---}
               SUB   WORD PTR [$B804],AX
               JA    @DECRTIM2
               TEST  BYTE PTR [$B80D],01000000b
               JNZ   @DECRTIM2
               OR    BYTE PTR [$B80D],01000000b
               PUSH  AX
               MOV   AL,BYTE PTR [$B80B]
               AND   AL,BYTE PTR [$B802]
               POP   AX
               JNS   @DECRTIM3
               OR    BYTE PTR [$B800],10000000b
@DECRTIM3:     TEST  BYTE PTR [$B80E],01000000b
               JZ    @DECRTIM2
               OR    BYTE PTR [IRQ_NMI],$01
               JMP   @DECRTIM2
@DECRTIM1:     {---t1 free run mode---}
               SUB   WORD PTR [$B804],AX
               JA    @DECRTIM2
               PUSH  AX
               MOV   AX,WORD PTR [$B806]
               ADD   WORD PTR [$B804],AX
               OR    BYTE PTR [$B80D],01000000b
               MOV   AL,BYTE PTR [$B80B]
               AND   AL,BYTE PTR [$B802]
               POP   AX
               JNS   @DECRTIM4
               XOR   BYTE PTR [$B800],10000000b
@DECRTIM4:     TEST  BYTE PTR [$B80E],01000000b
               JZ    @DECRTIM2
               OR    BYTE PTR [IRQ_NMI],$01
@DECRTIM2:     CMP   BYTE PTR [IRQ_NMI],$00
               JZ    @DECRTIM6
               JNS   @IRQOCC
               {---nmi---}
               PUSH  AX
               INC   BYTE PTR [CS:NMIDELAY]
               MOV   AL,BYTE PTR [CS:NMIRESPONSE]
               CMP   BYTE PTR [CS:NMIDELAY],AL
               POP   AX
               JB    @DECRTIM6
               AND   BYTE PTR [IRQ_NMI],$7F
               MOV   BYTE PTR [CS:NMIDELAY],$00
               PUSH  AX
               MOV   AX,SI
               AND   BP,$00FF
               MOV   BYTE PTR [DS:BP+STACKBASE],AH
               DEC   BP
               AND   BP,$00FF
               MOV   BYTE PTR [DS:BP+STACKBASE],AL
               DEC   BP
               AND   BP,$00FF
               MOV   BYTE PTR [DS:BP+STACKBASE],BH
               DEC   BP
               OR    BH,00000100b {set interrupt disable flag}
               AND   BH,11110111b {clear decimal mode flag}
               CALL  FDC_NMI_HANDLER {call fdc}
               MOV   SI,WORD PTR [NMI_VECTOR]
               POP   AX
               JMP   @DECRTIM6
@IRQOCC:       {---irq---}
               TEST  BH,00000100b {test interrupt disable flag}
               JNZ   @DECRTIM6
               INC   BYTE PTR [CS:IRQDELAY]
               CMP   BYTE PTR [CS:IRQDELAY],$02
               JB    @DECRTIM6
               AND   BYTE PTR [IRQ_NMI],$FC
               MOV   BYTE PTR [CS:IRQDELAY],$00
               PUSH  AX
               MOV   AX,SI
               AND   BP,$00FF
               MOV   BYTE PTR [DS:BP+STACKBASE],AH
               DEC   BP
               AND   BP,$00FF
               MOV   BYTE PTR [DS:BP+STACKBASE],AL
               DEC   BP
               AND   BP,$00FF
               MOV   AL,BH
               AND   AL,11101111b {clear break flag}
               MOV   BYTE PTR [DS:BP+STACKBASE],AL
               DEC   BP
               OR    BH,00000100b {set interrupt disable flag}
               AND   BH,11110111b {clear decimal mode flag}
               MOV   SI,WORD PTR [IRQ_VECTOR]
               POP   AX
@DECRTIM6:     ADD   WORD PTR [AANTCYCLES],AX
               CMP   BYTE PTR [CS:CPUSPEEDMODE],$00
               JNZ   @NEXTOPC3
               SHL   AX,1
               MOV   DI,AX
               MOV   AX,WORD PTR PCWAITTABLE[CS:DI]
               SUB   AX,+90-15
               SUB   AX,WORD PTR [PCCYCLES]
               JS    @NEXTOPC6
               JZ    @NEXTOPC3
               MOV   DI,WORD PTR [WACHTSCHULD]
               OR    DI,DI
               JNZ   @NEXTOPC5
@NEXTOPC8:     SHR   AX,1
               JZ    @NEXTOPC3
               NEG   AX
               ADD   AX,+4000+OFFSET SPEEDLOOP {4000=size of speedloop}
               CALL  AX
               JMP   @NEXTOPC3
@NEXTOPC5:     CMP   AX,DI
               JAE   @NEXTOPC7
               SUB   WORD PTR [WACHTSCHULD],AX
               JMP   @NEXTOPC3
@NEXTOPC7:     MOV   WORD PTR [WACHTSCHULD],$0000
               SUB   AX,DI
               JZ    @NEXTOPC3
               JMP   @NEXTOPC8
@NEXTOPC6:     NEG   AX
               ADD   WORD PTR [WACHTSCHULD],AX
@NEXTOPC3:     MOV   WORD PTR [PCCYCLES],$0000
               DEC   WORD PTR [COUNTER]
               JNZ   @DBGSWAPBYTE2
               MOV   WORD PTR [COUNTER],$3FFF
               MOV   AL,BYTE PTR TOETS[CS:$1D] {---ctrl+f12---}
               AND   AL,BYTE PTR TOETS[CS:$58]
               AND   AL,$03
               JZ    @NEXTOPC9
               MOV   DS,WORD PTR [CS:DATASEG]
               CALL  WRITEFOUTBUF
               JMP   @ENDOFEMUL
@NEXTOPC9:     MOV   AL,BYTE PTR TOETS[CS:$38] {---alt+f12---}
               AND   AL,BYTE PTR TOETS[CS:$58]
               AND   AL,$03
               JNZ   @BOOT
@NEXTOPC21:    MOV   AL,BYTE PTR TOETS[CS:$2A] {---shift+f12---}
               OR    AL,BYTE PTR TOETS[CS:$36]
               AND   AL,BYTE PTR TOETS[CS:$58]
               AND   AL,$03
               JZ    @NEXTOPC1
               PUSH  DS
               PUSH  ES
               PUSHA
               MOV   DS,WORD PTR [CS:DATASEG]
               CALL  WRITEFOUTBUF
               CALL  @VOLUMEOFF
               CALL  @CLRINT
               CALL  TEMPDOSPROMPT
               CALL  INITATOMGRAPH
               MOV   AX,$A000
               MOV   ES,AX
               CALL  @SETINT
               POPA
               POP   ES
               POP   DS
               CALL  @VOLUMEON
               CALL  SETBORDERCOL
               CALL  SETINTENSCOL
               CALL  REBUILDSCREEN
               JMP   @DBGSWAPBYTE1
@NEXTOPC1:     TEST  BYTE PTR TOETS[CS:$3E],$03 {---f4---}
               JZ    @NEXTOPC12
               CALL  DISABLEMOUSE
               CALL  SWAPKEYBOARD
@NEXTOPC13:    TEST  BYTE PTR TOETS[CS:$3E],$03 {---f4---}
               JNZ   @NEXTOPC13
               CALL  ENABLEMOUSE
               CALL  REBUILDSCREEN
               JMP   @DBGSWAPBYTE1
@NEXTOPC12:    TEST  BYTE PTR TOETS[CS:$3F],$03 {---f5---}
               JZ    @NEXTOPC14
               CALL  DISABLEMOUSE
               CALL  SWAPCPUSPEED
@NEXTOPC15:    TEST  BYTE PTR TOETS[CS:$3F],$03 {---f5---}
               JNZ   @NEXTOPC15
               CALL  ENABLEMOUSE
               CALL  REBUILDSCREEN
               JMP   @DBGSWAPBYTE1
@NEXTOPC14:    TEST  BYTE PTR TOETS[CS:$40],$03 {---f6---}
               JZ    @NEXTOPC2
               CALL  DISABLEMOUSE
               CALL  BOXINFO
@NEXTOPC17:    TEST  BYTE PTR TOETS[CS:$40],$03 {---f6---}
               JNZ   @NEXTOPC17
               CALL  ENABLEMOUSE
               CALL  REBUILDSCREEN
               JMP   @DBGSWAPBYTE1
@NEXTOPC2:     TEST  BYTE PTR TOETS[CS:$37],$03 {---print scrn---}
               JZ    @NEXTOPC18
               CALL  DISABLEMOUSE
               PUSH  DS
               PUSH  ES
               PUSHA
               MOV   DS,WORD PTR [CS:DATASEG]
               CALL  WRITEBMP
               POPA
               POP   ES
               POP   DS
@NEXTOPC19:    TEST  BYTE PTR TOETS[CS:$37],$03 {---print scrn---}
               JNZ   @NEXTOPC19
               CALL  ENABLEMOUSE
               JMP   @DBGSWAPBYTE1
@NEXTOPC18:    TEST  BYTE PTR TOETS[CS:$58],$03 {---f12---}
               JZ    @DBGSWAPBYTE1
@NEXTOPC4:     TEST  BYTE PTR TOETS[CS:$58],$03 {---f12---}
               JNZ   @NEXTOPC4
               {---breakkey---}
@BREAKKEY:     PUSH  DS
               PUSH  ES
               PUSHA
               MOV   DS,WORD PTR [CS:DATASEG]
               CALL  WRITEFOUTBUF
               POPA
               POP   ES
               MOV   BYTE PTR FOUTOPEN,$00
               POP   DS
               CALL  CLRDRIVETXT
               TEST  BYTE PTR [CS:BOX0ONBREAK],$FF
               JZ    @BRKKEY1
               CMP   BYTE PTR [SCHAKELBYTE],$00
               JZ    @BRKKEY1
               CALL  SAVEZP90
               MOV   BYTE PTR [SCHAKELBYTE],$00
               CALL  SETA000MEM
@BRKKEY1:      MOV   BYTE PTR [CS:AANTBOXRET],$00
               MOV   BYTE PTR [CS:ALTKEYB],$00
               MOV   BYTE PTR [CS:CPUSPEEDMODE],$00
               MOV   DS,WORD PTR [CS:ATOMSEG]
               MOV   BX,$2000
               MOV   BYTE PTR [CS:ACCU_B],$00
               SUB   CX,CX
               SUB   DX,DX
               MOV   WORD PTR [$B800],CX
               MOV   WORD PTR [$B802],CX
               MOV   BYTE PTR [$B80B],CL
               MOV   WORD PTR [$B80C],CX
               MOV   WORD PTR [$B80E],CX
               MOV   BYTE PTR [CS:T2L_L],CL
               MOV   BYTE PTR [$BFE2],$07
               MOV   BYTE PTR [CS:MOUSENR],$80 {mouse off}
               MOV   BYTE PTR [IRQ_NMI],CL
               MOV   BYTE PTR [CS:IRQDELAY],CL
               MOV   BYTE PTR [CS:NMIDELAY],CL
               MOV   WORD PTR [$0202],CX
               MOV   BYTE PTR [FLIPFLOP],$55
               TEST  BYTE PTR [CS:LEENDERTSROM],$FF
               JZ    @BRKKEY2
               {---initialize fp-rom: determine co-processor type---}
               MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE1],AL
               PUSH  AX
               MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE2],AL
               PUSH  AX
               MOV   SI,$DBA9
@INITFPROM1:   LODSB
               MOV   AH,$00
               SHL   AX,1
               MOV   DI,AX
               MOV   AX,WORD PTR @OPCODETABLE[DI]
               CALL  AX
               CMP   SI,$DBB1
               JNZ   @INITFPROM1
               POP   AX
               MOV   BYTE PTR [CS:@DBGSWAPBYTE2],AL
               POP   AX
               MOV   BYTE PTR [CS:@DBGSWAPBYTE1],AL
@BRKKEY2:      MOV   SI,WORD PTR [RES_VECTOR]
               JMP   @DBGSWAPBYTE2
@DBGSWAPBYTE1: {@DBGSWAPBYTE1 can be RETN byte-swapped}
               TEST  BYTE PTR TOETS[CS:$42],$03 {---f8---}
               JZ    @NEXTOPC20
               MOV   BYTE PTR @LASTMENU,$04
               CALL  @SHOWMENU
               JMP   @DBGSWAPBYTE2
@NEXTOPC20:    TEST  BYTE PTR TOETS[CS:$43],$03 {---f9---}
               JZ    @NEXTOPC10
               MOV   BYTE PTR @LASTMENU,$01
               CALL  @SHOWMENU
               JMP   @DBGSWAPBYTE2
@NEXTOPC10:    TEST  BYTE PTR TOETS[CS:$44],$03 {---f10---}
               JZ    @NEXTOPC16
               MOV   BYTE PTR @LASTMENU,$02
               CALL  @SHOWMENU
               JMP   @DBGSWAPBYTE2
@NEXTOPC16:    TEST  BYTE PTR TOETS[CS:$57],$03 {---f11---}
               JZ    @DBGSWAPBYTE2
               MOV   BYTE PTR @LASTMENU,$03
               CALL  @SHOWMENU
@DBGSWAPBYTE2: {@DBGSWAPBYTE2 can be RETN byte-swapped}
               MOV   AL,BYTE PTR [SI]
               INC   SI
               MOV   AH,$00
               SHL   AX,1
               MOV   DI,AX
               JMP   WORD PTR @OPCODETABLE[DI]

{---[lda/ldx/ldy_via]-------------------------------------------------------}
@LDX_VIA:      CALL  @GETVIAREG
               MOV   CL,AL
               OR    AL,AL
               JMP   @UPDATENZ
@LDY_VIA:      CALL  @GETVIAREG
               MOV   DL,AL
               OR    AL,AL
               JMP   @UPDATENZ
@LDA_VIA:      CALL  @GETVIAREG
               MOV   BL,AL
               OR    AL,AL
               JMP   @UPDATENZ
@BIT_VIA:      CALL  @GETVIAREG
               JMP   @OPC2C_1
@GETVIAREG:    MOV   AL,BYTE PTR [DI]
               AND   DI,$000F
               SHL   DI,1
               MOV   DI,WORD PTR @VIAGETTABLE[DI]
               OR    DI,DI
               JZ    @GETVIA1
               JMP   DI
@GETVIA1:      RETN

@GETB801:      PUSH  DS
               PUSH  ES
               PUSHA
               MOV   AH,$02
               SUB   DX,DX
               INT   $17
               TEST  AH,00100000b {test: out of paper}
               JZ    @GETB801_1
@GETB801_2:    POPA
               POP   ES
               POP   DS
               {---printer out of paper---}
               MOV   AL,$FF
               XOR   AL,BYTE PTR [$B803]
               RETN
@GETB801_1:    TEST  AH,10010000b {test: not busy, selected}
               JZ    @GETB801_2
               POPA
               POP   ES
               POP   DS
               {---printer ready---}
               MOV   AL,$00
               RETN

@GETB804:      MOV   AL,BYTE PTR [$B804]
               AND   BYTE PTR [$B80D],10111111b
               RETN

@GETB808:      MOV   AL,BYTE PTR [$B808]
               AND   BYTE PTR [$B80D],11011111b
               RETN

@GETB80C:      PUSH  DS
               PUSH  ES
               PUSHA
               MOV   AH,$02
               SUB   DX,DX
               INT   $17
               TEST  AH,00001001b {test: I/O error, timeout}
               JZ    @GETB80C_1
               {---printer not ready---}
               POPA
               POP   ES
               POP   DS
               MOV   AL,$00
               MOV   BYTE PTR [$B80C],AL
               RETN
@GETB80C_1:    {---printer ready---}
               POPA
               POP   ES
               POP   DS
               MOV   AL,BYTE PTR [$B80C]
               RETN

@GETB80D:      MOV   AL,BYTE PTR [$B80D]
               AND   AL,01111111b
               TEST  AL,BYTE PTR [$B80E]
               JZ    @GETB80D_1
               OR    AL,10000000b
@GETB80D_1:    RETN

@GETB80E:      MOV   AL,BYTE PTR [$B80E]
               OR    AL,$80
               RETN

@GETB80F:      MOV   AL,BYTE PTR [$B800]
               RETN

{---[sta/stx/sty/stz_via]---------------------------------------------------}
@STZ_VIA:      MOV   AL,$00
               JMP   @STOREVIA1
@STX_VIA:      MOV   AL,CL
               JMP   @STOREVIA1
@STY_VIA:      MOV   AL,DL
               JMP   @STOREVIA1
@STA_VIA:      MOV   AL,BL
@STOREVIA1:    AND   DI,$000F
               SHL   DI,1
               JMP   WORD PTR @VIASTORETABLE[DI]

@STOREB801:    MOV   BYTE PTR [$B801],AL
               JMP   @NEXTOPC

@STOREB804:    MOV   BYTE PTR [$B806],AL
               JMP   @NEXTOPC

@STOREB805:    MOV   BYTE PTR [$B807],AL
               MOV   AH,AL
               MOV   AL,BYTE PTR [$B806]
               MOV   WORD PTR [$B804],AX
               AND   BYTE PTR [$B80D],10111111b
               MOV   AL,BYTE PTR [$B80B]
               AND   AL,BYTE PTR [$B802]
               JNS   @STB805_1
               AND   BYTE PTR [$B800],01111111b
@STB805_1:     MOV   AL,BYTE PTR [INSTRCYCLES]
               MOV   AH,$00
               JMP   @DECRTIM2

@STOREB808:    MOV   BYTE PTR [CS:T2L_L],AL
               JMP   @NEXTOPC

@STOREB809:    MOV   AH,AL
               MOV   AL,BYTE PTR [CS:T2L_L]
               MOV   WORD PTR [$B808],AX
               AND   BYTE PTR [$B80D],11011111b
               MOV   AL,BYTE PTR [INSTRCYCLES]
               MOV   AH,$00
               JMP   @DECRTIM2

@STOREB80C:    MOV   BYTE PTR [$B80C],AL
               AND   AL,$0F
               CMP   AL,$0C
               JNZ   @STB80C_1
               PUSH  DS
               PUSH  ES
               PUSHA
               MOV   AH,$00
               MOV   AL,BYTE PTR [$B801]
               SUB   DX,DX
               INT   $17
               POPA
               POP   ES
               POP   DS
@STB80C_1:     JMP   @NEXTOPC

@STOREB80D:    OR    BYTE PTR [$B80D],AL
               JMP   @NEXTOPC

@STOREB80E:    OR    AL,AL
               JS    @STB80E_1
               NOT   AL
               AND   BYTE PTR [$B80E],AL
               JMP   @NEXTOPC
@STB80E_1:     OR    BYTE PTR [$B80E],AL
               JMP   @NEXTOPC

@STOREB80F:    MOV   BYTE PTR [$B800],AL
               JMP   @NEXTOPC

@STOREB8xx:    SHR   DI,1
               MOV   BYTE PTR [$B800+DI],AL
               JMP   @NEXTOPC

{---[store_mousex]----------------------------------------------------------}
@STZ_MOUSEX:   MOV   AL,$00
               JMP   @STOREMX
@STA_MOUSEX:   MOV   AL,BL
               JMP   @STOREMX
@STX_MOUSEX:   MOV   AL,CL
               JMP   @STOREMX
@STY_MOUSEX:   MOV   AL,DL
@STOREMX:      CMP   AL,$F8
               JBE   @STMX1
               MOV   AL,$F8
@STMX1:        CLI
               PUSH  ES
               MOV   DI,$A000
               MOV   ES,DI
               PUSH  WORD PTR [CS:MOUSENR]
               CALL  CLRMOUSECURSOR
               MOV   BYTE PTR [$BFE0],AL
               JMP   @NEWPOSMOUSE
{---[store_mousey]----------------------------------------------------------}
@STZ_MOUSEY:   MOV   AL,$00
               JMP   @STOREMY
@STA_MOUSEY:   MOV   AL,BL
               JMP   @STOREMY
@STX_MOUSEY:   MOV   AL,CL
               JMP   @STOREMY
@STY_MOUSEY:   MOV   AL,DL
@STOREMY:      CMP   AL,$47
               JAE   @STMY1
               MOV   AL,$47
@STMY1:        CLI
               PUSH  ES
               MOV   DI,$A000
               MOV   ES,DI
               PUSH  WORD PTR [CS:MOUSENR]
               CALL  CLRMOUSECURSOR
               MOV   BYTE PTR [$BFE1],AL
@NEWPOSMOUSE:  MOV   ES,WORD PTR [CS:DATASEG]
               MOV   AL,BYTE PTR [$BFE0]
               MOV   BYTE PTR TEMPMOUSEDAT[ES:$00],AL
               MOV   AH,$00
               SHL   AX,1
               MOV   WORD PTR TEMPMOUSEDAT[ES:$03],AX
               MOV   AL,BYTE PTR [$BFE1]
               MOV   BYTE PTR TEMPMOUSEDAT[ES:$01],AL
               SUB   AL,+64
               MOV   AH,$00
               SHL   AX,1
               SUB   AX,+511
               NEG   AX
               MOV   WORD PTR TEMPMOUSEDAT[ES:$05],AX
               POP   AX {---[cs:mousenr]---}
               MOV   DI,$A000
               MOV   ES,DI
               CALL  SETMOUSECURSOR
               MOV   ES,WORD PTR [CS:DATASEG]
               PUSH  DS
               PUSHA
               MOV   AX,$0004
               MOV   CX,WORD PTR TEMPMOUSEDAT[ES:$03]
               MOV   DX,WORD PTR TEMPMOUSEDAT[ES:$05]
               INT   $33
               POPA
               POP   DS
               POP   ES
               STI
               JMP   @NEXTOPC

{---[store_mousenr]---------------------------------------------------------}
@STORE_MOUSENR:CLI
               CALL  CLRMOUSECURSOR
               CALL  SETMOUSECURSOR
               STI
               JMP   @NEXTOPC

{---[trace]-----------------------------------------------------------------}
@TRACE:        MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE1],AL
               PUSH  AX
               MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE2],AL
               PUSH  AX
               MOV   SI,WORD PTR [CS:PROGRAMCNT]
@TRACE1:       MOV   BP,WORD PTR [CS:STACKPOINTER]
               MOV   BL,BYTE PTR [CS:ACCUMULATOR]
               MOV   BH,BYTE PTR [CS:FLAGREGISTER]
               MOV   CL,BYTE PTR [CS:XREGISTER]
               MOV   DL,BYTE PTR [CS:YREGISTER]
               MOV   DS,WORD PTR [CS:ATOMSEG]
               LODSB
               MOV   AH,$00
               SHL   AX,1
               MOV   DI,AX
               MOV   AX,WORD PTR @OPCODETABLE[DI]
               CALL  AX
               MOV   WORD PTR [CS:PROGRAMCNT],SI
               MOV   WORD PTR [CS:STACKPOINTER],BP
               MOV   BYTE PTR [CS:ACCUMULATOR],BL
               MOV   BYTE PTR [CS:FLAGREGISTER],BH
               MOV   BYTE PTR [CS:XREGISTER],CL
               MOV   BYTE PTR [CS:YREGISTER],DL
               POP   AX
               MOV   BYTE PTR [CS:@DBGSWAPBYTE2],AL
               POP   AX
               MOV   BYTE PTR [CS:@DBGSWAPBYTE1],AL
               RETN

{---[step]------------------------------------------------------------------}
@STEP:         MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE1],AL
               PUSH  AX
               MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE2],AL
               PUSH  AX
               MOV   SI,WORD PTR [CS:PROGRAMCNT]
               MOV   BYTE PTR [CS:TRACEORSTEP],$00
               CMP   BYTE PTR[SI],$20 {---jsr---}
               JNZ   @TRACE1
               MOV   BYTE PTR [CS:TRACEORSTEP],$01
               MOV   AX,SI
               ADD   AX,$03
@STEP4:        MOV   WORD PTR @STEPENDOFS,AX
               PUSH  SI
               CALL  SETCOLORS
               POP   SI
               SUB   DI,DI
               MOV   CX,$4000
               MOV   AL,$FF
@STEP5:        STOSB
               STOSB
               STOSB
               INC   AL
               STOSB
               DEC   AL
               LOOP  @STEP5
               CALL  ENABLEMOUSE
               MOV   BP,WORD PTR [CS:STACKPOINTER]
               MOV   BL,BYTE PTR [CS:ACCUMULATOR]
               MOV   BH,BYTE PTR [CS:FLAGREGISTER]
               MOV   CL,BYTE PTR [CS:XREGISTER]
               MOV   DL,BYTE PTR [CS:YREGISTER]
               MOV   DS,WORD PTR [CS:ATOMSEG]
               CALL  SETBORDERCOL
               CALL  REBUILDSCREEN
@STEP1:        LODSB
               MOV   AH,$00
               SHL   AX,1
               MOV   DI,AX
               MOV   AX,WORD PTR @OPCODETABLE[DI]
               CALL  AX
               MOV   AL,BYTE PTR TOETS[CS:$3B] {---f1---}
               OR    AL,BYTE PTR TOETS[CS:$42] {---f8---}
               OR    AL,BYTE PTR TOETS[CS:$43] {---f9---}
               OR    AL,BYTE PTR TOETS[CS:$44] {---f10---}
               OR    AL,BYTE PTR TOETS[CS:$57] {---f11---}
               AND   AL,$03
               JNZ   @STEP3
               CMP   SI,WORD PTR @STEPENDOFS
               JNZ   @STEP1
               JMP   @STEP2
@STEP3:        MOV   AL,BYTE PTR TOETS[CS:$3B] {---f1---}
               OR    AL,BYTE PTR TOETS[CS:$42] {---f8---}
               OR    AL,BYTE PTR TOETS[CS:$43] {---f9---}
               OR    AL,BYTE PTR TOETS[CS:$44] {---f10---}
               OR    AL,BYTE PTR TOETS[CS:$57] {---f11---}
               AND   AL,$03
               JNZ   @STEP3
@STEP2:        MOV   WORD PTR [CS:PROGRAMCNT],SI
               MOV   WORD PTR [CS:STACKPOINTER],BP
               MOV   BYTE PTR [CS:ACCUMULATOR],BL
               MOV   BYTE PTR [CS:FLAGREGISTER],BH
               MOV   BYTE PTR [CS:XREGISTER],CL
               MOV   BYTE PTR [CS:YREGISTER],DL
               CALL  DISABLEMOUSE
               POP   AX
               MOV   BYTE PTR [CS:@DBGSWAPBYTE2],AL
               POP   AX
               MOV   BYTE PTR [CS:@DBGSWAPBYTE1],AL
               RETN

{---[untilcursor]-----------------------------------------------------------}
@UNTILCURSOR:  MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE1],AL
               PUSH  AX
               MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE2],AL
               PUSH  AX
@UNTILCURS1:   TEST  BYTE PTR TOETS[CS:$23],$03 {---h---}
               JNZ   @UNTILCURS1
               MOV   SI,WORD PTR [CS:PROGRAMCNT]
               MOV   AX,WORD PTR [CS:DISASPTR]
               JMP   @STEP4

{---[breakpoint]------------------------------------------------------------}
@BREAKPOINT:   PUSH  DS
               MOV   AX,CS
               MOV   DS,AX
               MOV   BYTE PTR CURSORX,+10
               MOV   BYTE PTR CURSORY,+6
               MOV   BL,$0C
               MOV   AL,01000101b
               CALL  PRINTCHAR
               MOV   CX,+18
               MOV   AL,01001100b
@BRKPNT2:      CALL  PRINTCHAR
               LOOP  @BRKPNT2
               MOV   AL,01001010b
               CALL  PRINTCHAR
               MOV   CL,+7
@BRKPNT3:      MOV   BYTE PTR CURSORX,+10
               MOV   BYTE PTR CURSORY,CL
               MOV   AL,01010101b
               CALL  PRINTCHAR
               MOV   BYTE PTR CURSORX,+29
               MOV   AL,01101010b
               CALL  PRINTCHAR
               INC   CL
               CMP   CL,+12
               JBE   @BRKPNT3
               MOV   BYTE PTR CURSORX,+10
               MOV   BYTE PTR CURSORY,+13
               MOV   AL,01010100b
               CALL  PRINTCHAR
               MOV   CX,+18
               MOV   AL,01001100b
@BRKPNT4:      CALL  PRINTCHAR
               LOOP  @BRKPNT4
               MOV   AL,01101000b
               CALL  PRINTCHAR
               CALL  PRINTSTRING
               DB    +11, +7,$0E,' ADD BRKP :       ',$00
               CALL  PRINTSTRING
               DB    +11, +8,$0E,'                  ',$00
               CALL  PRINTSTRING
               DB    +11, +9,$0E,' REMOVE   :       ',$00
               CALL  PRINTSTRING
               DB    +11,+10,$0E,' REMOVE   :       ',$00
               CALL  PRINTSTRING
               DB    +11,+11,$0E,' REMOVE   :       ',$00
               CALL  PRINTSTRING
               DB    +11,+12,$0E,' REMOVE   :       ',$00
               MOV   BYTE PTR CURSORX,+12
               MOV   BYTE PTR CURSORY,+7
               MOV   AL,'A' AND $3F
               MOV   BL,$0F
               CALL  PRINTCHAR
               MOV   CL,'1'
@BRKPNT5:      MOV   BYTE PTR CURSORX,+19
               MOV   AL,CL
               ADD   AL,+9-'1'
               MOV   BYTE PTR CURSORY,AL
               MOV   AL,CL
               CALL  PRINTCHAR
               INC   CL
               CMP   CL,'4'
               JBE   @BRKPNT5
               MOV   BYTE PTR CURSORX,+23
               MOV   BYTE PTR CURSORY,+7
               MOV   AL,BYTE PTR [CS:HEXTEKEN]
               MOV   BL,$09
               CALL  PRINTCHAR
               MOV   AX,WORD PTR [CS:DISASPTR]
               CALL  PRINTWORD
               MOV   BL,$0E
               SUB   CX,CX
@BRKPNT7:      MOV   AL,$01
               SHL   AL,CL
               TEST  BYTE PTR [CS:BRKPNTON],AL
               JZ    @BRKPNT8
               MOV   BYTE PTR CURSORX,+23
               MOV   AL,CL
               ADD   AL,+9
               MOV   BYTE PTR CURSORY,AL
               MOV   AL,BYTE PTR [CS:HEXTEKEN]
               MOV   BL,$0E
               CALL  PRINTCHAR
               MOV   SI,CX
               SHL   SI,1
               MOV   AX,WORD PTR BRKPNTS[CS:SI]
               CALL  PRINTWORD
@BRKPNT8:      INC   CL
               CMP   CL,$04
               JNZ   @BRKPNT7
@BRKPNT6:      TEST  BYTE PTR TOETS[CS:$30],$03 {---b---}
               JNZ   @BRKPNT6
@BRKPNT9:      TEST  BYTE PTR TOETS[CS:$1E],$03 {---a---}
               JZ    @BRKPNT10
               CMP   BYTE PTR [CS:BRKPNTON],$0F
               JAE   @BRKPNT10
               MOV   AX,WORD PTR [CS:DISASPTR]
               SUB   CX,CX
@BRKPNT11:     MOV   BL,$01
               SHL   BL,CL
               TEST  BYTE PTR [CS:BRKPNTON],BL
               JZ    @BRKPNT12
               MOV   SI,CX
               SHL   SI,1
               CMP   AX,WORD PTR BRKPNTS[CS:SI]
               JZ    @BRKPNT10
@BRKPNT12:     INC   CL
               CMP   CL,$04
               JNZ   @BRKPNT11
               SUB   CX,CX
@BRKPNT14:     MOV   BL,$01
               SHL   BL,CL
               TEST  BYTE PTR [CS:BRKPNTON],BL
               JZ    @BRKPNT13
               INC   CL
               JMP   @BRKPNT14
@BRKPNT13:     MOV   SI,CX
               SHL   SI,1
               MOV   WORD PTR BRKPNTS[CS:SI],AX
               OR    BYTE PTR [CS:BRKPNTON],BL
               JMP   @BRKPNT15
@BRKPNT10:     MOV   BX,$0002
@BRKPNT17:     TEST  BYTE PTR TOETS[CS:BX],$03 {---1/2/3/4---}
               JZ    @BRKPNT16
               MOV   CL,BL
               SUB   CL,$02
               MOV   AL,$01
               SHL   AL,CL
               TEST  BYTE PTR [CS:BRKPNTON],AL
               JZ    @BRKPNT16
               XOR   AL,$0F
               AND   BYTE PTR [CS:BRKPNTON],AL
               JMP   @BRKPNT15
@BRKPNT16:     INC   BL
               CMP   BL,$05
               JBE   @BRKPNT17
               TEST  BYTE PTR TOETS[CS:$01],$03 {---esc---}
               JZ    @BRKPNT9
@BRKPNT15:     MOV   AL,BYTE PTR TOETS[CS:$01] {---esc---}
               OR    AL,BYTE PTR TOETS[CS:$1E] {---a---}
               OR    AL,BYTE PTR TOETS[CS:$02] {---1---}
               OR    AL,BYTE PTR TOETS[CS:$03] {---2---}
               OR    AL,BYTE PTR TOETS[CS:$04] {---3---}
               OR    AL,BYTE PTR TOETS[CS:$05] {---4---}
               AND   AL,$03
               JNZ   @BRKPNT15
               POP   DS
               RETN

{---[showmenu]--------------------------------------------------------------}
@SHOWMENU:     MOV   WORD PTR [CS:PROGRAMCNT],SI
               MOV   WORD PTR [CS:STACKPOINTER],BP
               MOV   BYTE PTR [CS:ACCUMULATOR],BL
               MOV   BYTE PTR [CS:FLAGREGISTER],BH
               MOV   BYTE PTR [CS:XREGISTER],CL
               MOV   BYTE PTR [CS:YREGISTER],DL
               CALL  DISABLEMOUSE
               MOV   DX,$03C8
               MOV   AL,$07
               OUT   DX,AL
               INC   DX
               MOV   AL,$00
               OUT   DX,AL
               OUT   DX,AL
               OUT   DX,AL
               CALL  UPPERLINES
               MOV   AL,BYTE PTR @LASTMENU
               OR    AL,AL
               JNZ   @SHOWMENU4
               MOV   AL,$01
@SHOWMENU4:    CMP   AL,$01
               JNZ   @SHOWMENU5
               CALL  TAPE
               JMP   @SHOWMENU3
@SHOWMENU5:    CMP   AL,$02
               JNZ   @SHOWMENU6
               CALL  OPTIONS
               JMP   @SHOWMENU3
@SHOWMENU6:    CMP   AL,$03
               JNZ   @SHOWMENU8
               CALL  MONITOR
               JMP   @SHOWMENU3
@SHOWMENU8:    CALL  DISK
@SHOWMENU3:    OR    AL,AL
               JZ    @SHOWMENU1
               MOV   BYTE PTR @LASTMENU,AL
               JMP   @SHOWMENU4
@SHOWMENU1:    TEST  BYTE PTR TOETS[CS:$01],$03 {---escape---}
               JNZ   @SHOWMENU1
               CALL  SETCOLORS
               SUB   DI,DI
               MOV   CX,$4000
               MOV   AL,$FF
@SHOWMENU2:    STOSB
               STOSB
               STOSB
               INC   AL
               STOSB
               DEC   AL
               LOOP  @SHOWMENU2
               CALL  ENABLEMOUSE
               MOV   SI,WORD PTR [CS:PROGRAMCNT]
               MOV   BP,WORD PTR [CS:STACKPOINTER]
               MOV   BL,BYTE PTR [CS:ACCUMULATOR]
               MOV   BH,BYTE PTR [CS:FLAGREGISTER]
               MOV   CL,BYTE PTR [CS:XREGISTER]
               MOV   DL,BYTE PTR [CS:YREGISTER]
               MOV   DS,WORD PTR [CS:ATOMSEG]
               CALL  SETBORDERCOL
               CALL  SETINTENSCOL
               CALL  REBUILDSCREEN
               TEST  BYTE PTR [CS:BRKPNTON],$0F
               JNZ   @SHOWMENU7
               RETN
@SHOWMENU7:    {---execute until breakpoint or f1 (exit debug mode)---}
               MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE1],AL
               PUSH  AX
               MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE2],AL
               PUSH  AX
@BREAKP1:      LODSB
               MOV   AH,$00
               SHL   AX,1
               MOV   DI,AX
               MOV   AX,WORD PTR @OPCODETABLE[DI]
               CALL  AX
               MOV   AL,BYTE PTR TOETS[CS:$3B] {---f1---}
               OR    AL,BYTE PTR TOETS[CS:$42] {---f8---}
               OR    AL,BYTE PTR TOETS[CS:$43] {---f9---}
               OR    AL,BYTE PTR TOETS[CS:$44] {---f10---}
               OR    AL,BYTE PTR TOETS[CS:$57] {---f11---}
               AND   AL,$03
               JNZ   @BREAKP3
               MOV   AL,BYTE PTR [CS:BRKPNTON]
               TEST  AL,00000001b
               JZ    @BREAKP4
               CMP   SI,WORD PTR BRKPNTS[CS:$0000]
               JZ    @BREAKP2
@BREAKP4:      TEST  AL,00000010b
               JZ    @BREAKP5
               CMP   SI,WORD PTR BRKPNTS[CS:$0002]
               JZ    @BREAKP2
@BREAKP5:      TEST  AL,00000100b
               JZ    @BREAKP6
               CMP   SI,WORD PTR BRKPNTS[CS:$0004]
               JZ    @BREAKP2
@BREAKP6:      TEST  AL,00001000b
               JZ    @BREAKP1
               CMP   SI,WORD PTR BRKPNTS[CS:$0006]
               JZ    @BREAKP2
               JMP   @BREAKP1
@BREAKP3:      MOV   BYTE PTR @LASTMENU,$03
               TEST  BYTE PTR TOETS[CS:$43],$03
               JZ    @BREAKP9
               MOV   BYTE PTR @LASTMENU,$01
@BREAKP9:      TEST  BYTE PTR TOETS[CS:$44],$03
               JZ    @BREAKP7
               MOV   BYTE PTR @LASTMENU,$02
@BREAKP7:      MOV   AL,BYTE PTR TOETS[CS:$3B] {---f1---}
               OR    AL,BYTE PTR TOETS[CS:$42] {---f8---}
               OR    AL,BYTE PTR TOETS[CS:$43] {---f9---}
               OR    AL,BYTE PTR TOETS[CS:$44] {---f10---}
               OR    AL,BYTE PTR TOETS[CS:$57] {---f11---}
               AND   AL,$03
               JNZ   @BREAKP7
               JMP   @BREAKP8
@BREAKP2:      MOV   BYTE PTR @LASTMENU,$03
@BREAKP8:      MOV   WORD PTR [CS:DISASPTR],SI
               POP   AX
               MOV   BYTE PTR [CS:@DBGSWAPBYTE2],AL
               POP   AX
               MOV   BYTE PTR [CS:@DBGSWAPBYTE1],AL
               JMP   @SHOWMENU

{---[resetandload; commandline in 0100h preset (including 0Dh,0Ah)]---------}
@RESETANDLOAD: MOV   BYTE PTR [CS:AANTBOXRET],$00
               MOV   DS,WORD PTR [CS:ATOMSEG]
               CALL  SETBORDERCOL
               CALL  REBUILDSCREEN
               MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE1],AL
               PUSH  AX
               MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE2],AL
               PUSH  AX
               MOV   BYTE PTR [CS:AANTBOXRET],$00
               MOV   BX,$2000
               MOV   BYTE PTR [CS:ACCU_B],$00
               SUB   CX,CX
               SUB   DX,DX
               MOV   WORD PTR [$B800],CX
               MOV   WORD PTR [$B802],CX
               MOV   BYTE PTR [$B80B],CL
               MOV   WORD PTR [$B80C],CX
               MOV   WORD PTR [$B80E],CX
               MOV   BYTE PTR [CS:T2L_L],CL
               MOV   BYTE PTR [$BFE2],$07
               MOV   BYTE PTR [CS:MOUSENR],$80 {mouse off}
               MOV   BYTE PTR [IRQ_NMI],CL
               MOV   BYTE PTR [CS:IRQDELAY],CL
               MOV   BYTE PTR [CS:NMIDELAY],CL
               MOV   WORD PTR [$0202],CX
               MOV   SI,WORD PTR [RES_VECTOR]
@RESANDLOAD1:  LODSB
               MOV   AH,$00
               SHL   AX,1
               MOV   DI,AX
               MOV   AX,WORD PTR @OPCODETABLE[DI]
               CALL  AX
               CMP   SI,$C2D2
               JNZ   @RESANDLOAD1
               MOV   DI,$00FF
               MOV   AL,'>'
               XCHG  AL,BYTE PTR [DI]
               PUSH  AX
@RESANDLOAD4:  MOV   BL,BYTE PTR [DI]
               PUSH  DI
               MOV   SI,$FFEF
@RESANDLOAD2:  LODSB
               MOV   AH,$00
               SHL   AX,1
               MOV   DI,AX
               MOV   AX,WORD PTR @OPCODETABLE[DI]
               CALL  AX
               CMP   SI,$FFF2
               JNZ   @RESANDLOAD2
               POP   DI
               CMP   BL,$0A
               JZ    @RESANDLOAD3
               INC   DI
               JMP   @RESANDLOAD4
@RESANDLOAD3:  POP   AX
               MOV   BYTE PTR [$00FF],AL
               MOV   BYTE PTR [$0007],$00
               MOV   SI,$C2D5
               POP   AX
               MOV   BYTE PTR [CS:@DBGSWAPBYTE2],AL
               POP   AX
               MOV   BYTE PTR [CS:@DBGSWAPBYTE1],AL
               JMP   @DBGSWAPBYTE2

{---[boot]------------------------------------------------------------------}
@BOOT:         MOV   AL,BYTE PTR TOETS[CS:$38] {---alt+f12---}
               AND   AL,BYTE PTR TOETS[CS:$58]
               AND   AL,$03
               JNZ   @BOOT
               MOV   WORD PTR [$0100],'TS'
               MOV   WORD PTR [$0102],'RA'
               MOV   WORD PTR [$0104],'0T'
               MOV   WORD PTR [$0106],$0A0D
               JMP   @RESETANDLOAD

{---[setint]----------------------------------------------------------------}
@SETINT:       CLI
               PUSH  DS
               SUB   AX,AX
               MOV   DS,AX
               MOV   AX,WORD PTR [$0020]
               MOV   WORD PTR @ORGIRQVEC[CS:$0000],AX
               MOV   AX,WORD PTR [$0022]
               MOV   WORD PTR @ORGIRQVEC[CS:$0002],AX
               MOV   AX,OFFSET @IRQHANDLER
               MOV   WORD PTR [$0020],AX
               MOV   WORD PTR [$0022],CS
               MOV   AX,WORD PTR [$0024]
               MOV   WORD PTR @ORGKEYVEC[CS:$0000],AX
               MOV   AX,WORD PTR [$0026]
               MOV   WORD PTR @ORGKEYVEC[CS:$0002],AX
               MOV   AX,OFFSET @KEYHANDLER
               MOV   WORD PTR [$0024],AX
               MOV   WORD PTR [$0026],CS
               MOV   AX,WORD PTR [$006C]
               MOV   WORD PTR @ORGBRKVEC[CS:$0000],AX
               MOV   AX,WORD PTR [$006E]
               MOV   WORD PTR @ORGBRKVEC[CS:$0002],AX
               MOV   AX,OFFSET @BRKHANDLER
               MOV   WORD PTR [$006C],AX
               MOV   WORD PTR [$006E],CS
               MOV   AL,$36
               OUT   $43,AL
               MOV   AL,$00
               OUT   $40,AL
               OUT   $40,AL
               PUSH  ES
               MOV   AX,CS
               MOV   ES,AX
               MOV   DI,OFFSET TOETS
               MOV   CX,$0082
               MOV   AL,$00
               CLD
               REPZ
               STOSB
               SUB   AX,AX
               INT   $33
               CMP   AX,$FFFF
               JNZ   @SETINT1
               MOV   AX,$000C
               MOV   CX,$007F
               MOV   DX,OFFSET @MOUSEHANDLER
               PUSH  CS
               POP   ES
               INT   $33
               MOV   AX,$0007
               SUB   CX,CX
               MOV   DX,$01F0
               INT   $33
               MOV   AX,$0008
               MOV   CX,+128
               MOV   DX,+496
               INT   $33
               MOV   AX,$0004
               SUB   CX,CX
               MOV   DX,+128
               INT   $33
               MOV   DS,WORD PTR [CS:ATOMSEG]
               MOV   BYTE PTR [$BFE0],0
               MOV   BYTE PTR [$BFE1],+255
@SETINT1:      POP   ES
               STI
               POP   DS
               RETN

{---[clrint]----------------------------------------------------------------}
@CLRINT:       PUSH  DS
               CLI
               SUB   AX,AX
               MOV   DS,AX
               MOV   AX,WORD PTR @ORGIRQVEC[CS:$0000]
               MOV   WORD PTR [$0020],AX
               MOV   AX,WORD PTR @ORGIRQVEC[CS:$0002]
               MOV   WORD PTR [$0022],AX
               MOV   AX,WORD PTR @ORGKEYVEC[CS:$0000]
               MOV   WORD PTR [$0024],AX
               MOV   AX,WORD PTR @ORGKEYVEC[CS:$0002]
               MOV   WORD PTR [$0026],AX
               MOV   AX,WORD PTR @ORGBRKVEC[CS:$0000]
               MOV   WORD PTR [$006C],AX
               MOV   AX,WORD PTR @ORGBRKVEC[CS:$0002]
               MOV   WORD PTR [$006E],AX
               SUB   AX,AX
               INT   $33
               STI
               POP   DS
               RETN

{---[mousehandler]----------------------------------------------------------}
@MOUSEHANDLER: PUSH  DS
               PUSH  ES
               PUSHA
               MOV   SI,$A000
               MOV   ES,SI
               MOV   AH,BYTE PTR [CS:MOUSENR]
               TEST  AL,$01
               JZ    @MOUSEH1
               CALL  CLRMOUSECURSOR
@MOUSEH1:      MOV   DS,WORD PTR [CS:ATOMSEG]
               SHR   CX,1
               MOV   BYTE PTR [$BFE0],CL
               NEG   DX
               ADD   DX,+511
               SHR   DX,1
               ADD   DL,+64
               MOV   BYTE PTR [$BFE1],DL
               XOR   BL,$07
               MOV   BYTE PTR [$BFE2],BL
               TEST  AL,$01
               JZ    @MOUSEH2
               TEST  AH,$80
               JNZ   @MOUSEH2
               MOV   AL,BYTE PTR [CS:MOUSENR]
               AND   AL,$1F
               CALL  SETMOUSECURSOR
@MOUSEH2:      POPA
               POP   ES
               POP   DS
               RETF

{---[keyhandler]------------------------------------------------------------}
@KEYHANDLER:   PUSH  AX
               PUSH  DI
               IN    AL,$60
               MOV   AH,AL
               IN    AL,$61
               OR    AL,$80
               OUT   $61,AL
               AND   AL,$7F
               OUT   $61,AL
               MOV   AL,AH
               MOV   AH,$00
               OR    AL,AL
               JNS   @KEYHND6
               AND   AL,$7F
               MOV   DI,AX
               MOV   BYTE PTR TOETS[CS:DI],$00
               CMP   AL,$48
               JB    @KEYHND4
               JNZ   @KEYHND7
               AND   BYTE PTR TOETS[CS:$80],$FE
               JMP   @KEYHND4
@KEYHND7:      CMP   AL,$50
               JNZ   @KEYHND8
               AND   BYTE PTR TOETS[CS:$80],$FD
               JMP   @KEYHND4
@KEYHND8:      CMP   AL,$4B
               JNZ   @KEYHND9
               AND   BYTE PTR TOETS[CS:$81],$FE
               JMP   @KEYHND4
@KEYHND9:      CMP   AL,$4D
               JNZ   @KEYHND4
               AND   BYTE PTR TOETS[CS:$81],$FD
@KEYHND4:      MOV   AL,$20
               OUT   $20,AL
               POP   DI
               POP   AX
@BRKHANDLER:   IRET
@KEYHND6:      MOV   DI,AX
               MOV   BYTE PTR TOETS[CS:DI],$01
               CMP   AL,$48
               JB    @KEYHND4
               JNZ   @KEYHND10
               OR    BYTE PTR TOETS[CS:$80],$01
               JMP   @KEYHND4
@KEYHND10:     CMP   AL,$50
               JNZ   @KEYHND11
               OR    BYTE PTR TOETS[CS:$80],$02
               JMP   @KEYHND4
@KEYHND11:     CMP   AL,$4B
               JNZ   @KEYHND12
               OR    BYTE PTR TOETS[CS:$81],$01
               JMP   @KEYHND4
@KEYHND12:     CMP   AL,$4D
               JNZ   @KEYHND4
               OR    BYTE PTR TOETS[CS:$81],$02
               JMP   @KEYHND4

{---[irqhandler]------------------------------------------------------------}
@IRQHANDLER:   INC   BYTE PTR [CS:KEYRELEASETEL]
               DB    $2E,$FF,$2E
               DW    OFFSET @ORGIRQVEC

{---[loadfile]--------------------------------------------------------------}
@LOADFILE:     PUSH  DS
               PUSH  ES
               PUSH  BX
               PUSH  CX
               PUSH  DX
               PUSH  BP
               PUSH  CX {---offset loadtable---}
               PUSH  WORD PTR [CS:LASTATM] {---file pointer---}
               PUSH  CS {---segment exitcode---}
               PUSH  OFFSET @LOADCODE {---offset exitcode---}
               MOV   DS,WORD PTR [CS:DATASEG]
               CALL  LOAD
               MOV   AX,$A000
               MOV   ES,AX
               SUB   DI,DI
               MOV   CX,$4000
               MOV   AL,$FF
@LOADFILE4:    STOSB
               STOSB
               STOSB
               INC   AL
               STOSB
               DEC   AL
               LOOP  @LOADFILE4
               POP   BP
               POP   DX
               POP   CX
               POP   BX
               POP   ES
               POP   DS
               CALL  SETBORDERCOL
               CALL  REBUILDSCREEN
               MOV   AX,WORD PTR @LOADCODE
               TEST  AH,$80
               JZ    @LOADFILE1
               MOV   SI,$F9FD
               JMP   @NEXTOPC {---generate checksum error 6---}
@LOADFILE1:    TEST  AH,$40
               JNZ   @LOADFILE3
               {---load ok---}
               MOV   WORD PTR [CS:LASTATM],AX
@LOADFILE2:    TEST  BYTE PTR TOETS[CS:$1C],$FF {---enter---}
               JNZ   @LOADFILE2
               JMP   @OPCODE60 {---rts---}
@LOADFILE3:    {---frozen file---}
               AND   AH,$3F
               MOV   WORD PTR [CS:LASTATM],AX
               MOV   SI,WORD PTR [CS:PROGRAMCNT]
               MOV   BP,WORD PTR [CS:STACKPOINTER]
               MOV   BL,BYTE PTR [CS:ACCUMULATOR]
               MOV   BH,BYTE PTR [CS:FLAGREGISTER]
               MOV   CL,BYTE PTR [CS:XREGISTER]
               MOV   DL,BYTE PTR [CS:YREGISTER]
               JMP   @NEXTOPC

{---[savefile]--------------------------------------------------------------}
@SAVEFILE:     PUSH  DS
               PUSH  ES
               PUSH  BX
               PUSH  CX
               PUSH  DX
               PUSH  BP
               PUSH  CX {---offset savetable---}
               PUSH  WORD PTR [CS:LASTATM] {---file pointer---}
               PUSH  CS {---segment exitcode---}
               PUSH  OFFSET @SAVECODE {---offset exitcode---}
               MOV   DS,WORD PTR [CS:DATASEG]
               CALL  SAVE
               POP   BP
               POP   DX
               POP   CX
               POP   BX
               POP   ES
               POP   DS
               MOV   AX,WORD PTR @SAVECODE
               TEST  AH,$80
               JNZ   @SAVEFILE1
               {---save ok---}
               INC   WORD PTR [CS:LASTATM]
               JMP   @OPCODE60 {---rts---}
@SAVEFILE1:    MOV   SI,$F9FD
               JMP   @NEXTOPC {---generate checksum error 6---}

{---[getbyte]---------------------------------------------------------------}
@GETBYTE:      PUSH  DS
               PUSH  SI
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   SI,WORD PTR FINBUFPTR
               CMP   SI,WORD PTR FINSIZE
               JAE   @GETB1
               ADD   SI,WORD PTR FINBUFOFS
               INC   WORD PTR FINBUFPTR
               MOV   DS,WORD PTR FINBUFSEG
               MOV   BL,BYTE PTR [SI]
               JMP   @GETB2
@GETB1:        MOV   BL,$0D
@GETB2:        POP   SI
               POP   DS
               JMP   @OPCODE60

{---[putbyte]---------------------------------------------------------------}
@PUTBYTE:      PUSH  DS
               MOV   DS,WORD PTR [CS:DATASEG]
               TEST  BYTE PTR FOUTOPEN,$FF
               JNZ   @PUTB2
               POP   DS
               MOV   SI,$F9FD
               JMP   @NEXTOPC {---generate checksum error 6---}
@PUTB2:        PUSH  DI
               MOV   DI,WORD PTR FOUTBUFPTR
               ADD   DI,WORD PTR FOUTBUFOFS
               MOV   DS,WORD PTR FOUTBUFSEG
               MOV   BYTE PTR [DI],BL
               POP   DI
               MOV   DS,WORD PTR [CS:DATASEG]
               INC   WORD PTR FOUTBUFPTR
               CMP   WORD PTR FOUTBUFPTR,FOUTBUFSIZE
               JB    @PUTB1
               PUSH  ES
               PUSHA
               CALL  WRITEFOUTBUF
               POPA
               POP   ES
@PUTB1:        POP   DS
               JMP   @OPCODE60

{---[finfoutcmd (see also finfoutcmd preparation at @OPCODE28)]-------------}
@FINFOUTCMD:   PUSH  DS
               PUSH  ES
               PUSHA
               TEST  BH,$01 {test carry}
               JZ    @FINFOUT1
               {---fin---}
               PUSH  WORD PTR @FILENAMEOFS
               PUSH  WORD PTR [CS:LASTATM] {---file pointer---}
               PUSH  CS {---segment exitcode---}
               PUSH  OFFSET @LOADCODE {---offset exitcode---}
               MOV   DS,WORD PTR [CS:DATASEG]
               CALL  READFINBUF
               POPA
               POP   ES
               POP   DS
               MOV   AX,WORD PTR @LOADCODE
               TEST  AH,$80
               JZ    @FINFOUT5
               MOV   SI,$F9FD
               JMP   @NEXTOPC {---generate checksum error 6---}
@FINFOUT5:     MOV   WORD PTR [CS:LASTATM],AX
               MOV   BL,$0D {---return filehandle---}
               JMP   @OPCODE60
@FINFOUT1:     {---fout---}
               PUSH  DS
               PUSHA
               MOV   DS,WORD PTR [CS:DATASEG]
               CALL  WRITEFOUTBUF
               POPA
               POP   DS
               MOV   ES,WORD PTR [CS:DATASEG]
               MOV   SI,WORD PTR @FILENAMEOFS
               SUB   BX,BX
@FINFOUT4:     MOV   AL,BYTE PTR [SI+BX]
               CMP   AL,$0D
               JZ    @FINFOUT3
               MOV   BYTE PTR [ES:FOUTNAME+$01+BX],AL
               INC   BL
               CMP   BL,$10
               JB    @FINFOUT4
@FINFOUT3:     MOV   BYTE PTR [ES:FOUTNAME],BL
               OR    BL,BL
               JNZ   @FINFOUT2
               MOV   BYTE PTR [ES:FOUTNAME],$04
               MOV   WORD PTR [ES:FOUTNAME+$01],'IF'
               MOV   WORD PTR [ES:FOUTNAME+$03],'EL'
@FINFOUT2:     MOV   DS,WORD PTR [CS:DATASEG]
               SUB   BX,BX
@FINFOUT6:     MOV   AL,BYTE PTR TAPEIMAGENAME[BX]
               MOV   BYTE PTR IMAGEFOUTNAME[BX],AL
               INC   BL
               CMP   BL,$09
               JB    @FINFOUT6
               MOV   BYTE PTR FOUTOPEN,$01
               MOV   WORD PTR FOUTBUFPTR,$0000
               CALL  CREATEFOUT
               POPA
               POP   ES
               POP   DS
               MOV   BL,$0D {---return filehandle---}
               JMP   @OPCODE60

{---[tapecat]---------------------------------------------------------------}
@TAPECAT:      PUSH  ES
               PUSHA
               MOV   ES,WORD PTR [CS:DATASEG]
               CMP   BYTE PTR [ES:AANTALTAPEIMAGES],$00
               JZ    @CAT2
               MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE1],AL
               PUSH  AX
               MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE2],AL
               PUSH  ES
               PUSHA
               PUSH  WORD PTR [@STEPENDOFS]
               {---check rest of *cat command for searchstring---}
               MOV   BYTE PTR CATSEARCH[ES:$00],$00
               MOV   BX,DX
               DEC   BX
@CAT19:        INC   BX
               CMP   BYTE PTR [$0100+BX],' '
               JZ    @CAT19
               SUB   SI,SI
@CAT15:        MOV   AL,BYTE PTR [$0100+BX]
               CMP   AL,'"'
               JZ    @CAT17
               CMP   AL,$0D
               JZ    @CAT18
               MOV   BYTE PTR CATSEARCH[ES:SI],AL
               INC   SI
               CMP   SI,$0010
               JZ    @CAT23
@CAT17:        INC   BX
               CMP   AL,'*'
               JNZ   @CAT15
@CAT18:        MOV   BYTE PTR CATSEARCH[ES:SI],$00
@CAT23:        {---name of tape image---}
               MOV   AX,WORD PTR [CS:LASTTAPE]
               MOV   CX,STR8GROOTTE
               MUL   CX
               MOV   SI,AX
               MOV   BX,$0001
@CAT11:        MOV   AL,BYTE PTR TAPEIMAGES[ES:SI+BX]
               CMP   AL,$40
               JB    @CAT14
               ADD   AL,$20
               JMP   @CAT13
@CAT14:        ADD   AL,$60
@CAT13:        MOV   BYTE PTR [BX+$00EC],AL
               INC   BL
               CMP   BL,BYTE PTR TAPEIMAGES[ES:SI]
               JBE   @CAT11
               MOV   BYTE PTR [BX+$00EC],$0D
               MOV   AX,$A000
               MOV   ES,AX
               {---print name of tape image---}
               MOV   DL,$00 {y-reg=00h}
               MOV   SI,$FA4A
               MOV   WORD PTR @STEPENDOFS,$FA4D
@CAT10:        LODSB
               MOV   AH,$00
               SHL   AX,1
               MOV   DI,AX
               MOV   AX,WORD PTR @OPCODETABLE[DI]
               CALL  AX
               CMP   SI,WORD PTR @STEPENDOFS
               JNZ   @CAT10
               {---go to next line---}
               MOV   SI,$FA5D
               MOV   WORD PTR @STEPENDOFS,$FA60
@CAT12:        LODSB
               MOV   AH,$00
               SHL   AX,1
               MOV   DI,AX
               MOV   AX,WORD PTR @OPCODETABLE[DI]
               CALL  AX
               CMP   SI,WORD PTR @STEPENDOFS
               JNZ   @CAT12
               POP   WORD PTR [@STEPENDOFS]
               POPA
               POP   ES
               MOV   BYTE PTR [CS:@DBGSWAPBYTE2],AL
               POP   AX
               MOV   BYTE PTR [CS:@DBGSWAPBYTE1],AL
               {---contents of tape image---}
               SUB   DX,DX
               SUB   SI,SI
@CAT1:         CMP   DX,WORD PTR [ES:AANTALATOMFILES]
               JZ    @CAT2
               SUB   BX,BX
@CAT22:        MOV   AL,BYTE PTR CATSEARCH[ES:BX]
               CMP   AL,$00
               JZ    @CAT16
               CMP   AL,'*'
               JZ    @CAT16
               CMP   AL,BYTE PTR ATOMFILES[ES:SI+BX]
               JNZ   @CAT20
               INC   BL
               CMP   BL,$10
               JB    @CAT22
@CAT16:        {---name ok for searchstring---}
               SUB   BX,BX
@CAT4:         MOV   AL,BYTE PTR ATOMFILES[ES:SI+BX] {filename}
               OR    AL,AL
               JNZ   @CAT3
               MOV   AL,' '
@CAT3:         MOV   BYTE PTR [$00ED+BX],AL
               INC   BL
               CMP   BL,$10
               JB    @CAT4
               MOV   BYTE PTR [$00ED+BX],$0D
               MOV   AX,WORD PTR ATOMFILES[ES:SI+$0010] {strtaddr}
               MOV   WORD PTR [$00D4],AX
               MOV   AX,WORD PTR ATOMFILES[ES:SI+$0012] {execaddr}
               MOV   WORD PTR [$00D6],AX
               MOV   AX,WORD PTR ATOMFILES[ES:SI+$0014] {datasize}
               MOV   WORD PTR [$00D9],AX
               MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE1],AL
               PUSH  AX
               MOV   AL,$C3 {retn}
               XCHG  BYTE PTR [CS:@DBGSWAPBYTE2],AL
               PUSH  ES
               PUSHA
               PUSH  WORD PTR [@STEPENDOFS]
               MOV   AX,$A000
               MOV   ES,AX
               {---print filename, strtaddr and execaddr---}
               MOV   DL,$00 {y-reg=00h}
               MOV   SI,$FA4A
               MOV   WORD PTR @STEPENDOFS,$FA50
@CAT5:         LODSB
               MOV   AH,$00
               SHL   AX,1
               MOV   DI,AX
               MOV   AX,WORD PTR @OPCODETABLE[DI]
               CALL  AX
               CMP   SI,WORD PTR @STEPENDOFS
               JNZ   @CAT5
               {---print hi-byte of datasize---}
               MOV   SI,$F7FA
               MOV   WORD PTR @STEPENDOFS,$F7FD
               MOV   BL,[$00DA] {acc=hi-byte}
@CAT7:         LODSB
               MOV   AH,$00
               SHL   AX,1
               MOV   DI,AX
               MOV   AX,WORD PTR @OPCODETABLE[DI]
               CALL  AX
               CMP   SI,WORD PTR @STEPENDOFS
               JNZ   @CAT7
               {---print lo-byte of datasize---}
               MOV   SI,$F7FA
               MOV   WORD PTR @STEPENDOFS,$F7FD
               MOV   BL,[$00D9] {acc=lo-byte}
@CAT8:         LODSB
               MOV   AH,$00
               SHL   AX,1
               MOV   DI,AX
               MOV   AX,WORD PTR @OPCODETABLE[DI]
               CALL  AX
               CMP   SI,WORD PTR @STEPENDOFS
               JNZ   @CAT8
               {---go to next line---}
               MOV   SI,$FA5D
               MOV   WORD PTR @STEPENDOFS,$FA60
@CAT6:         LODSB
               MOV   AH,$00
               SHL   AX,1
               MOV   DI,AX
               MOV   AX,WORD PTR @OPCODETABLE[DI]
               CALL  AX
               CMP   SI,WORD PTR @STEPENDOFS
               JNZ   @CAT6
               POP   WORD PTR [@STEPENDOFS]
               POPA
               POP   ES
               MOV   BYTE PTR [CS:@DBGSWAPBYTE2],AL
               POP   AX
               MOV   BYTE PTR [CS:@DBGSWAPBYTE1],AL
@CAT20:        INC   DX
               ADD   SI,ATMRECGROOTTE
               MOV   AL,BYTE PTR TOETS[CS:$01] {---escape---}
               OR    AL,BYTE PTR TOETS[CS:$1D] {---ctrl---}
               AND   AL,$03
               JZ    @CAT1
@CAT9:         MOV   AL,BYTE PTR TOETS[CS:$01] {---escape---}
               OR    AL,BYTE PTR TOETS[CS:$1D] {---ctrl---}
               AND   AL,$03
               JNZ   @CAT9
@CAT2:         POPA
               POP   ES
               JMP   @OPCODE60

{---[volumeon]--------------------------------------------------------------}
@VOLUMEON:     CMP   BYTE PTR @SBAVAIL,$00
               JNZ   @VOLON1
               IN    AL,$61
               AND   AL,$FC
               OUT   $61,AL
               RETN
@VOLON1:       PUSH  DS
               PUSH  DX
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   DX,WORD PTR IOPORT
               ADD   DL,$0C
               MOV   AL,$D1
               CALL  OUTBYTE
               POP   DX
               POP   DS
               RETN

{---[volumeoff]-------------------------------------------------------------}
@VOLUMEOFF:    CMP   BYTE PTR @SBAVAIL,$00
               JNZ   @VOLOFF1
               IN    AL,$61
               AND   AL,$FC
               OUT   $61,AL
               RETN
@VOLOFF1:      PUSH  DS
               PUSH  DX
               MOV   DS,WORD PTR [CS:DATASEG]
               MOV   DX,WORD PTR IOPORT
               ADD   DL,$0C
               MOV   AL,$D3
               CALL  OUTBYTE
               POP   DX
               POP   DS
               RETN

{---[data]------------------------------------------------------------------}
@OPCODETABLE:  DW    OFFSET @OPCODE00
               DW    OFFSET @OPCODE01
               DW    OFFSET @OPCODE02
               DW    OFFSET @OPCODE03
               DW    OFFSET @OPCODE04
               DW    OFFSET @OPCODE05
               DW    OFFSET @OPCODE06
               DW    OFFSET @OPCODE07
               DW    OFFSET @OPCODE08
               DW    OFFSET @OPCODE09
               DW    OFFSET @OPCODE0A
               DW    OFFSET @OPCODE0B
               DW    OFFSET @OPCODE0C
               DW    OFFSET @OPCODE0D
               DW    OFFSET @OPCODE0E
               DW    OFFSET @OPCODE0F
               DW    OFFSET @OPCODE10
               DW    OFFSET @OPCODE11
               DW    OFFSET @OPCODE12
               DW    OFFSET @OPCODE13
               DW    OFFSET @OPCODE14
               DW    OFFSET @OPCODE15
               DW    OFFSET @OPCODE16
               DW    OFFSET @OPCODE17
               DW    OFFSET @OPCODE18
               DW    OFFSET @OPCODE19
               DW    OFFSET @OPCODE1A
               DW    OFFSET @OPCODE1B
               DW    OFFSET @OPCODE1C
               DW    OFFSET @OPCODE1D
               DW    OFFSET @OPCODE1E
               DW    OFFSET @OPCODE1F
               DW    OFFSET @OPCODE20
               DW    OFFSET @OPCODE21
               DW    OFFSET @OPCODE22
               DW    OFFSET @OPCODE23
               DW    OFFSET @OPCODE24
               DW    OFFSET @OPCODE25
               DW    OFFSET @OPCODE26
               DW    OFFSET @OPCODE27
               DW    OFFSET @OPCODE28
               DW    OFFSET @OPCODE29
               DW    OFFSET @OPCODE2A
               DW    OFFSET @OPCODE2B
               DW    OFFSET @OPCODE2C
               DW    OFFSET @OPCODE2D
               DW    OFFSET @OPCODE2E
               DW    OFFSET @OPCODE2F
               DW    OFFSET @OPCODE30
               DW    OFFSET @OPCODE31
               DW    OFFSET @OPCODE32
               DW    OFFSET @OPCODE33
               DW    OFFSET @OPCODE34
               DW    OFFSET @OPCODE35
               DW    OFFSET @OPCODE36
               DW    OFFSET @OPCODE37
               DW    OFFSET @OPCODE38
               DW    OFFSET @OPCODE39
               DW    OFFSET @OPCODE3A
               DW    OFFSET @OPCODE3B
               DW    OFFSET @OPCODE3C
               DW    OFFSET @OPCODE3D
               DW    OFFSET @OPCODE3E
               DW    OFFSET @OPCODE3F
               DW    OFFSET @OPCODE40
               DW    OFFSET @OPCODE41
               DW    OFFSET @OPCODE42
               DW    OFFSET @OPCODE43
               DW    OFFSET @OPCODE44
               DW    OFFSET @OPCODE45
               DW    OFFSET @OPCODE46
               DW    OFFSET @OPCODE47
               DW    OFFSET @OPCODE48
               DW    OFFSET @OPCODE49
               DW    OFFSET @OPCODE4A
               DW    OFFSET @OPCODE4B
               DW    OFFSET @OPCODE4C
               DW    OFFSET @OPCODE4D
               DW    OFFSET @OPCODE4E
               DW    OFFSET @OPCODE4F
               DW    OFFSET @OPCODE50
               DW    OFFSET @OPCODE51
               DW    OFFSET @OPCODE52
               DW    OFFSET @OPCODE53
               DW    OFFSET @OPCODE54
               DW    OFFSET @OPCODE55
               DW    OFFSET @OPCODE56
               DW    OFFSET @OPCODE57
               DW    OFFSET @OPCODE58
               DW    OFFSET @OPCODE59
               DW    OFFSET @OPCODE5A
               DW    OFFSET @OPCODE5B
               DW    OFFSET @OPCODE5C
               DW    OFFSET @OPCODE5D
               DW    OFFSET @OPCODE5E
               DW    OFFSET @OPCODE5F
               DW    OFFSET @OPCODE60
               DW    OFFSET @OPCODE61
               DW    OFFSET @OPCODE62
               DW    OFFSET @OPCODE63
               DW    OFFSET @OPCODE64
               DW    OFFSET @OPCODE65
               DW    OFFSET @OPCODE66
               DW    OFFSET @OPCODE67
               DW    OFFSET @OPCODE68
               DW    OFFSET @OPCODE69
               DW    OFFSET @OPCODE6A
               DW    OFFSET @OPCODE6B
               DW    OFFSET @OPCODE6C
               DW    OFFSET @OPCODE6D
               DW    OFFSET @OPCODE6E
               DW    OFFSET @OPCODE6F
               DW    OFFSET @OPCODE70
               DW    OFFSET @OPCODE71
               DW    OFFSET @OPCODE72
               DW    OFFSET @OPCODE73
               DW    OFFSET @OPCODE74
               DW    OFFSET @OPCODE75
               DW    OFFSET @OPCODE76
               DW    OFFSET @OPCODE77
               DW    OFFSET @OPCODE78
               DW    OFFSET @OPCODE79
               DW    OFFSET @OPCODE7A
               DW    OFFSET @OPCODE7B
               DW    OFFSET @OPCODE7C
               DW    OFFSET @OPCODE7D
               DW    OFFSET @OPCODE7E
               DW    OFFSET @OPCODE7F
               DW    OFFSET @OPCODE80
               DW    OFFSET @OPCODE81
               DW    OFFSET @OPCODE82
               DW    OFFSET @OPCODE83
               DW    OFFSET @OPCODE84
               DW    OFFSET @OPCODE85
               DW    OFFSET @OPCODE86
               DW    OFFSET @OPCODE87
               DW    OFFSET @OPCODE88
               DW    OFFSET @OPCODE89
               DW    OFFSET @OPCODE8A
               DW    OFFSET @OPCODE8B
               DW    OFFSET @OPCODE8C
               DW    OFFSET @OPCODE8D
               DW    OFFSET @OPCODE8E
               DW    OFFSET @OPCODE8F
               DW    OFFSET @OPCODE90
               DW    OFFSET @OPCODE91
               DW    OFFSET @OPCODE92
               DW    OFFSET @OPCODE93
               DW    OFFSET @OPCODE94
               DW    OFFSET @OPCODE95
               DW    OFFSET @OPCODE96
               DW    OFFSET @OPCODE97
               DW    OFFSET @OPCODE98
               DW    OFFSET @OPCODE99
               DW    OFFSET @OPCODE9A
               DW    OFFSET @OPCODE9B
               DW    OFFSET @OPCODE9C
               DW    OFFSET @OPCODE9D
               DW    OFFSET @OPCODE9E
               DW    OFFSET @OPCODE9F
               DW    OFFSET @OPCODEA0
               DW    OFFSET @OPCODEA1
               DW    OFFSET @OPCODEA2
               DW    OFFSET @OPCODEA3
               DW    OFFSET @OPCODEA4
               DW    OFFSET @OPCODEA5
               DW    OFFSET @OPCODEA6
               DW    OFFSET @OPCODEA7
               DW    OFFSET @OPCODEA8
               DW    OFFSET @OPCODEA9
               DW    OFFSET @OPCODEAA
               DW    OFFSET @OPCODEAB
               DW    OFFSET @OPCODEAC
               DW    OFFSET @OPCODEAD
               DW    OFFSET @OPCODEAE
               DW    OFFSET @OPCODEAF
               DW    OFFSET @OPCODEB0
               DW    OFFSET @OPCODEB1
               DW    OFFSET @OPCODEB2
               DW    OFFSET @OPCODEB3
               DW    OFFSET @OPCODEB4
               DW    OFFSET @OPCODEB5
               DW    OFFSET @OPCODEB6
               DW    OFFSET @OPCODEB7
               DW    OFFSET @OPCODEB8
               DW    OFFSET @OPCODEB9
               DW    OFFSET @OPCODEBA
               DW    OFFSET @OPCODEBB
               DW    OFFSET @OPCODEBC
               DW    OFFSET @OPCODEBD
               DW    OFFSET @OPCODEBE
               DW    OFFSET @OPCODEBF
               DW    OFFSET @OPCODEC0
               DW    OFFSET @OPCODEC1
               DW    OFFSET @OPCODEC2
               DW    OFFSET @OPCODEC3
               DW    OFFSET @OPCODEC4
               DW    OFFSET @OPCODEC5
               DW    OFFSET @OPCODEC6
               DW    OFFSET @OPCODEC7
               DW    OFFSET @OPCODEC8
               DW    OFFSET @OPCODEC9
               DW    OFFSET @OPCODECA
               DW    OFFSET @OPCODECB
               DW    OFFSET @OPCODECC
               DW    OFFSET @OPCODECD
               DW    OFFSET @OPCODECE
               DW    OFFSET @OPCODECF
               DW    OFFSET @OPCODED0
               DW    OFFSET @OPCODED1
               DW    OFFSET @OPCODED2
               DW    OFFSET @OPCODED3
               DW    OFFSET @OPCODED4
               DW    OFFSET @OPCODED5
               DW    OFFSET @OPCODED6
               DW    OFFSET @OPCODED7
               DW    OFFSET @OPCODED8
               DW    OFFSET @OPCODED9
               DW    OFFSET @OPCODEDA
               DW    OFFSET @OPCODEDB
               DW    OFFSET @OPCODEDC
               DW    OFFSET @OPCODEDD
               DW    OFFSET @OPCODEDE
               DW    OFFSET @OPCODEDF
               DW    OFFSET @OPCODEE0
               DW    OFFSET @OPCODEE1
               DW    OFFSET @OPCODEE2
               DW    OFFSET @OPCODEE3
               DW    OFFSET @OPCODEE4
               DW    OFFSET @OPCODEE5
               DW    OFFSET @OPCODEE6
               DW    OFFSET @OPCODEE7
               DW    OFFSET @OPCODEE8
               DW    OFFSET @OPCODEE9
               DW    OFFSET @OPCODEEA
               DW    OFFSET @OPCODEEB
               DW    OFFSET @OPCODEEC
               DW    OFFSET @OPCODEED
               DW    OFFSET @OPCODEEE
               DW    OFFSET @OPCODEEF
               DW    OFFSET @OPCODEF0
               DW    OFFSET @OPCODEF1
               DW    OFFSET @OPCODEF2
               DW    OFFSET @OPCODEF3
               DW    OFFSET @OPCODEF4
               DW    OFFSET @OPCODEF5
               DW    OFFSET @OPCODEF6
               DW    OFFSET @OPCODEF7
               DW    OFFSET @OPCODEF8
               DW    OFFSET @OPCODEF9
               DW    OFFSET @OPCODEFA
               DW    OFFSET @OPCODEFB
               DW    OFFSET @OPCODEFC
               DW    OFFSET @OPCODEFD
               DW    OFFSET @OPCODEFE
               DW    OFFSET @OPCODEFF

@VIASTORETABLE:DW    OFFSET @STOREB8xx
               DW    OFFSET @STOREB801
               DW    OFFSET @STOREB8xx
               DW    OFFSET @STOREB8xx
               DW    OFFSET @STOREB804
               DW    OFFSET @STOREB805
               DW    OFFSET @STOREB8xx
               DW    OFFSET @STOREB8xx
               DW    OFFSET @STOREB808
               DW    OFFSET @STOREB809
               DW    OFFSET @NEXTOPC
               DW    OFFSET @STOREB8xx
               DW    OFFSET @STOREB80C
               DW    OFFSET @STOREB80D
               DW    OFFSET @STOREB80E
               DW    OFFSET @STOREB80F

@VIAGETTABLE:  DW    $0000
               DW    OFFSET @GETB801
               DW    $0000
               DW    $0000
               DW    OFFSET @GETB804
               DW    $0000
               DW    $0000
               DW    $0000
               DW    OFFSET @GETB808
               DW    $0000
               DW    $0000
               DW    $0000
               DW    OFFSET @GETB80C
               DW    OFFSET @GETB80D
               DW    OFFSET @GETB80E
               DW    OFFSET @GETB80F

@ORGIRQVEC:    DD    $00000000
@ORGKEYVEC:    DD    $00000000
@ORGBRKVEC:    DD    $00000000
@PCSP:         DW    $0000

@SBAVAIL:      DB    $00

@STEPENDOFS:   DW    $0000

@LASTMENU:     DB    $00

@LOADCODE:     DW    $0000
@SAVECODE:     DW    $0000

@SCHAKELSTART: DB    $00
@FILENAMEOFS:  DW    $0000

@ENDOFPRG:
END;
FOR I := 0 TO 3 DO
  IF DISKETTENAMES[I] <> '' THEN CLOSE_DISK_IMAGE (I);
END.


{===========================================================================

BL = A

CL = X

DL = Y

BH flags  bit value  description                  pc-bit

           7  (80h)  N negative   1=NEG             7
           6  (40h)  V overflow   1=OVFL
           5  (20h)  -
           4  (10h)  B break
           3  (08h)  D decimal    1=DEC
           2  (04h)  I interrupt  1=DISABLE
           1  (02h)  Z zero       1=RESULT ZERO     6
           0  (01h)  C carry      1=TRUE            0

DS = segment of atom memory
SI = PC
BP = stackpointer (only lower 8 bits valid)

----------------------------------------------------------------------------
Memory heap requirements (for $m directive at top of code):

Atom memory              FFF8h
Extension boxes & data  101F0h
FIN buffer               FFF8h
FOUT buffer              1000h
Flt.Point PC buffer      0900h
Temporary buffers       10FF8h  (maximum wanted)
                        ------+
                        42AD8h = 273,112 bytes minimum required.