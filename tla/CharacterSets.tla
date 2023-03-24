--------------------------- MODULE CharacterSets ----------------------------
(***************************************************************************)
(* Some helper functions to convert back and forth between character       *)
(* sets and sequences of ordinals.                                         *)
(*                                                                         *)
(* This module takes advantage of TLC behavior that is technically a       *)
(* bug, so should only be used for ease of model input & output and        *)
(* avoided in the core of the spec itself. See:                            *)
(* https://github.com/tlaplus/tlaplus/issues/512#issuecomment-717468528    *)
(***************************************************************************)

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE Strings

\* The set of all printable ASCII characters, ordinals 32-126 inclusive
\* Backtick ` omitted; see https://github.com/tlaplus/tlaplus/issues/802
PrintableASCII ==
  " !\"#$%&'()*+,-./0123456789"
  \o ":;<=>?@ABCDEFGHIJKLMNOPQ"
  \o "RSTUVWXYZ[\\]^_ abcdefgh"
  \o "ijklmnopqrstuvwxyz{|}~"

\* The ordinal offset for the set of printable ASCII characters
PrintableASCIIOffset == 32

\* Given a character and a character set, returns its ordinal in the set
OrdinalFromCharSet(c, charSet, offset) ==
  offset + IndexOf(charSet, c)

\* Given an ordinal and a character set, returns the ordinal's character
CharFromOrdinal(ord, charSet, offset) ==
  Index(charSet, ord - offset)

\* Given a sequence of ordinals and a character set, returns the string
StrFromOrdinalSeq(seq, charSet, offset) ==
  IF seq = <<>>
  THEN ""
  ELSE StrFromSeq([
    i \in DOMAIN seq |->
      CharFromOrdinal(seq[i], charSet, offset)
  ])

============================================================================

