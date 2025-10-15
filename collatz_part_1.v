Require Import Nat.
Require Import List.
Import ListNotations.
Require Import Lia.   
Require Import PeanoNat.
Require Import Ring.
Require Import Arith.  
Require Import ArithRing.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.Div2.
Load "log2_p.v".


(* Define Collatz operations   Documentation uses Coq 8.10.2 version *)
Inductive CollatzOp : Type :=
  | R0 : CollatzOp
  | R1 : CollatzOp.

(* Define the property of valid input *)
Definition valid_input (n: nat) := n >= 1.

(* Helper definition: convert bool to Prop *)
Definition is_even (n: nat) := Nat.even n = true.
Definition is_odd (n: nat) := Nat.even n = false.

(* Define single-step Collatz operation *)
Definition collatz_step (n : nat) : nat :=
  if Nat.even n then n / 2
  else 3 * n + 1.

(* Entry function definition *)
Definition valid_R0R1_entry_number (d n: nat) : nat :=
  (2 * (2^d) * n) + (2^d - 2).

(* Define entry function *)
Definition valid_R0R0_entry_number (d n: nat) : nat :=
  n * (2^d).

(* R1R0 entry function definition *)
Definition valid_R1R0_entry_number (d n: nat) : nat :=
  (2 * (2^d) * n) + (2^d - 1).


(* Define counting function *)
Fixpoint count_R0 (ops: list CollatzOp) : nat :=
match ops with
| [] => 0
| R0 :: rest => S (count_R0 rest)
| R1 :: rest => count_R0 rest
end.

(* R1 counting function *)
Fixpoint count_R1 (ops: list CollatzOp) : nat :=
match ops with
| [] => 0
| R0 :: rest => count_R1 rest
| R1 :: rest => S (count_R1 rest)
end.


(* Define counting function for R0 and R1 in sequence *)
Fixpoint count_operations (ops: list CollatzOp) : (nat * nat) :=
  match ops with
  | nil => (0, 0)
  | op :: rest =>
    let (r0s, r1s) := count_operations rest in
    match op with
    | R0 => (S r0s, r1s)
    | R1 => (r0s, S r1s)
    end
  end.


(* Define valid operation *)
Definition valid_operation (n: nat) (op: CollatzOp) : Prop :=
  match op with
  | R0 => is_even n
  | R1 => is_odd n
  end.

(* Define the k-th value in sequence *)
Fixpoint nth_sequence_value (n: nat) (k: nat) : nat :=
  match k with
  | 0 => n
  | S k' => collatz_step (nth_sequence_value n k')
  end.

(* Define the final value of sequence *)
Definition sequence_end (n: nat) (ops: list CollatzOp) : nat :=
  nth_sequence_value n (length ops).
  
(* Define sequence validity: each operation in the sequence is legal *)
Definition valid_sequence (ops: list CollatzOp) (n: nat) : Prop :=
  forall i, i < length ops ->
    valid_operation (nth_sequence_value n i) (nth i ops R0).


(* R0 pattern repetition constructor - can handle single R0 and consecutive R0 *)
Fixpoint repeat_R0 (d: nat) : list CollatzOp :=
  match d with
  | 0 => []
  | S d' => R0 :: repeat_R0 d'
  end.
(*    This function constructs an operation list containing D consecutive R1R0 operation pairs *)
Fixpoint repeat_R1R0 (d: nat) : list CollatzOp :=
  match d with
  | 0 => []
  | S d' => R1 :: R0 :: repeat_R1R0 d'
  end.
  
(* Consecutive R0 pattern counting function *)
Fixpoint count_consecutive_R0 (ops: list CollatzOp) : nat :=
  match ops with
  | [] => 0
  | R0 :: rest => 1 + count_consecutive_R0 rest
  | _ => 0
  end.

(* Consecutive R1R0 pattern counting *)
Fixpoint count_consecutive_R1R0 (ops: list CollatzOp) : nat :=
  match ops with
  | [] => 0
  | [_] => 0
  | R1 :: R0 :: rest => S (count_consecutive_R1R0 rest)
  | _ :: rest => count_consecutive_R1R0 rest
  end.
  
(* Main theorem structure *)
Fixpoint build_k_steps (n: nat) (k: nat) : list CollatzOp :=
  match k with
  | 0 => []
  | S k' =>
    let prev_ops := build_k_steps n k' in
    let curr_n := sequence_end n prev_ops in
    if Nat.even curr_n
    then prev_ops ++ [R0]          (* Even: add R0 *)
    else prev_ops ++ [R1; R0]      (* Odd: add R1R0 *)
  end.
  
