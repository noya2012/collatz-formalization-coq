
(* noya2012@126.com 306000250@qq.com  zeng  *)

Load "collatz_part_4.v".



(* Helper lemma: R0 operations strictly decrease values *)
Lemma R0_strict_descent : forall n,
  valid_input n ->
  is_even n ->
  collatz_step n < n.
Proof.
intros n Hvalid Heven.
unfold collatz_step, is_even in *.
rewrite Heven.
assert (H: n >= 2). {
unfold valid_input in Hvalid.
apply Nat.even_spec in Heven.
destruct Heven as [k Hk].
rewrite Hk in *.
assert (k >= 1) by lia.
lia.
}
apply Nat.div_lt; lia.
Qed.






(* 偶数除以2后仍然有效 *)
Lemma valid_input_div2 : forall n,
  valid_input n ->
  is_even n ->
  valid_input (n / 2).
Proof.
intros n Hvalid Heven.
assert (valid_operation n R0) by (unfold valid_operation; auto).
assert (sequence_end n [R0] = n / 2).
{
unfold sequence_end.
simpl length.
unfold nth_sequence_value.
simpl.
unfold collatz_step.
unfold is_even in Heven.
destruct (Nat.even n); try discriminate Heven.
reflexivity.
}
assert (valid_sequence [R0] n).
{
unfold valid_sequence.
intros i Hi.
simpl in Hi.
destruct i; try lia.
simpl.
auto.
}
rewrite <- H0.
apply sequence_validity_preservation with (ops := [R0]); auto.
Qed.



(* 子序列有效性引理 *)
Lemma subsequence_valid : forall n op ops,
  valid_sequence (op :: ops) n ->
  valid_sequence ops (collatz_step n).
Proof.
intros n op ops Hvalid.
unfold valid_sequence in *.
intros i Hi.
assert (Hseq: forall k, k <= i ->
nth_sequence_value (collatz_step n) k = nth_sequence_value n (S k)).
{ intros k Hk.
induction k.
-
rewrite nth_sequence_value_0.
rewrite nth_sequence_value_succ.
reflexivity.
-
rewrite nth_sequence_value_succ.
rewrite IHk by lia.
rewrite nth_sequence_value_succ.
reflexivity. }
rewrite Hseq by lia.
specialize (Hvalid (S i)).
simpl in Hvalid.
apply Hvalid.
simpl. lia.
Qed.
(* 序列末尾值的有效性 *)
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

(* 添加第几个末尾值 *)
Lemma nth_append_last : forall (l : list CollatzOp) (x : CollatzOp),
  nth (length l) (l ++ [x]) R0 = x.
Proof.
induction l; simpl.
- reflexivity.
- apply IHl.
Qed.

(* 性质：添加R0后，R0计数增加1，R1计数不变 *)
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

(* 性质：添加R1R0后，R0计数增加1，R1计数增加1 *)
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

(* 性质：添加R1R0后，R0计数增加1，R1计数增加1 *)
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

(* R0和R1计数之和等于总长度的引理 *)
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
