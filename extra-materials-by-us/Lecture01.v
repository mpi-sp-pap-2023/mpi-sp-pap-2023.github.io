(** * Basics: Functional Programming in Coq *)

(* ################################################################# *)
(** * Data and Functions *)

(* ================================================================= *)
(** ** Enumerated Types *)

(** In Coq, we can build practically everything from first
    principles... *)

(* ================================================================= *)
(** ** Days of the Week *)

(** A datatype definition: *)

Inductive day : Type :=
  | monday 
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(** A function on days: *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | _  => monday
  end.

(** Simplification: *)

Compute (next_weekday friday).
(* ==> monday : day *)

Compute (next_weekday (next_weekday (saturday))).
(* ==> tuesday : day *)


(* ================================================================= *)
(** ** Booleans *)

(** Another familiar enumerated type: *)

Inductive bool : Type :=
  | true
  | false.

(** Booleans are also available from Coq's standard library, but
    in this course we'll define everything from scratch, just to see
    how it's done. *)
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(** Note the syntax for defining multi-argument
    functions ([andb] and [orb]).  *)

Compute (orb true false). 
(* ==> true : bool *)

Compute (orb false false). 
(* ==> false : bool *)

(** We can define new symbolic notations for existing definitions. *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Compute (false || false || true).
(* ==> true: bool *) 

(** We can also write these function using Coq's "if" expressions.  *)

Definition negb' (b:bool) : bool :=
  if b then false
  else true.

Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

(** This works for all datatypes with two constructors *)

Inductive bw : Type := 
  | b
  | w. 

Definition invert (x: bw) : bw := 
  if x then w
  else b.
  
Compute (invert b).
(* ==> w: bw *)

Compute (invert w).
(* ==> b: bw *)
