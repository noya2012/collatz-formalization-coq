
(* noya2012@126.com 306000250@qq.com  zeng  *)

Load "collatz_part_4.v".


(* Validity of sequence end value *)
Lemma sequence_end_valid : forall n ops,
  valid_input n ->
  valid_sequence ops n ->
  valid_input (sequence_end n ops).
Proof.
intros n ops Hvalid Hvalid_seq.
unfold sequence_end.
apply valid_sequence_inductive with (ops := ops).
- exact Hvalid.
- exact Hvalid_seq.
- reflexivity.
Qed.

(* Add the last element at position *)
Lemma nth_append_last : forall (l : list CollatzOp) (x : CollatzOp),
  nth (length l) (l ++ [x]) R0 = x.
Proof.
induction l; simpl.
- reflexivity.
- apply IHl.
Qed.

(* Property: After adding R0, R0 count increases by 1, R1 count remains unchanged *)
Lemma count_operations_app_R0 : forall ops,
  let (r0s, r1s) := count_operations ops in
  let (new_r0s, new_r1s) := count_operations (ops ++ [R0]) in
  new_r0s = r0s + 1 /\ new_r1s = r1s.
Proof.
induction ops as [|op ops' IH].
-
simpl.
split; reflexivity.
-
simpl.
destruct op.
+
destruct (count_operations ops') as [r0s' r1s'] eqn:Hold.
destruct (count_operations (ops' ++ [R0])) as [new_r0s' new_r1s'] eqn:Hnew.
destruct IH as [IH1 IH2].
simpl in *.
split.
*
rewrite IH1. reflexivity.
*
rewrite IH2. reflexivity.
+
destruct (count_operations ops') as [r0s' r1s'] eqn:Hold.
destruct (count_operations (ops' ++ [R0])) as [new_r0s' new_r1s'] eqn:Hnew.
destruct IH as [IH1 IH2].
simpl in *.
split.
*
rewrite IH1. reflexivity.
*
rewrite IH2. reflexivity.
Qed.

(* Property: After adding R1R0, R0 count increases by 1, R1 count increases by 1 *)
Lemma nth_append_two : forall (l : list CollatzOp) (x y : CollatzOp),
  nth (length l) (l ++ [x; y]) R0 = x /\
  nth (S (length l)) (l ++ [x; y]) R0 = y.
Proof.
intros l x y.
induction l; simpl.
- split; reflexivity.
- destruct (IHl) as [H1 H2].
split.
+ exact H1.
+ exact H2.
Qed.

(* Property: After adding R1R0, R0 count increases by 1, R1 count increases by 1 *)
Lemma count_operations_app_R1R0 : forall ops,
  let (r0s, r1s) := count_operations ops in
  let (r0s_new, r1s_new) := count_operations (ops ++ [R1; R0]) in
  r0s_new = S r0s /\ r1s_new = S r1s.
Proof.
intros ops.
induction ops as [|op ops' IH].
-
simpl.
split; reflexivity.
-
simpl.
destruct op;
destruct (count_operations ops') as [r0s' r1s'];
destruct (count_operations (ops' ++ [R1; R0])) as [r0s_new' r1s_new'];
destruct IH as [IH1 IH2].
+
split.
*
simpl. rewrite IH1. reflexivity.
*
simpl. rewrite IH2. reflexivity.
+
split.
*
simpl. rewrite IH1. reflexivity.
*
simpl. rewrite IH2. reflexivity.
Qed.

(* Lemma: Sum of R0 and R1 counts equals total length *)
Lemma count_sum_c2 : forall ops,
  let (r0s, r1s) := count_operations ops in
  r0s + r1s = length ops.
Proof.
induction ops as [|op ops' IH].
-
simpl. reflexivity.
-
simpl.
destruct (count_operations ops') as [r0s' r1s'].
assert (r0s' + r1s' = length ops') by exact IH.
destruct op.
+
simpl.
lia.
+
simpl.
lia.
Qed.
