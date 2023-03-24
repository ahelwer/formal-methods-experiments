----------------------------- MODULE Strings --------------------------------
(***************************************************************************)
(* Some helper functions on strings. Note that TLA⁺ doesn't have a         *)
(* notion of a character datatype, so these are represented by strings     *)
(* of length 1. Ordinals should be used in actual spec logic.              *)
(*                                                                         *)
(* This module takes advantage of TLC behavior that is technically a       *)
(* bug, so should only be used for ease of model input & output and        *)
(* avoided in the core of the spec itself. See:                            *)
(* https://github.com/tlaplus/tlaplus/issues/512#issuecomment-717468528    *)
(***************************************************************************)

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

\* Returns the ith characther in string s, indexed from 0
RECURSIVE Index(_, _)
Index(s, i) ==
  IF i = 0
  THEN Head(s)
  ELSE Index(Tail(s), i - 1)

\* Returns the index of the first occurrence character c in string s
RECURSIVE IndexOf(_, _)
IndexOf(s, c) ==
  IF Head(s) = c
  THEN 0
  ELSE 1 + IndexOf(Tail(s), c)

\* Given a string, converts it into a sequence of characters
RECURSIVE SeqFromStr(_)
SeqFromStr(s) ==
  IF s = ""
  THEN <<>>
  ELSE <<Head(s)>> \o SeqFromStr(Tail(s))

\* Given a sequence of characters, converts it into a string
RECURSIVE StrFromSeq(_)
StrFromSeq(seq) ==
  IF seq = <<>>
  THEN ""
  ELSE Head(seq) \o StrFromSeq(Tail(seq))

\* Given a string, returns the set of all characters in the string
RECURSIVE SetFromStr(_)
SetFromStr(s) ==
  IF s = ""
  THEN {}
  ELSE {Head(s)} \union SetFromStr(Tail(s))

=============================================================================

