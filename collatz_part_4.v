
Load "collatz_part_3.v".



(* 2. 单步操作的有效性 *)
Lemma single_step_valid : forall n op,
  valid_input n ->
  valid_operation n op ->
  valid_input (collatz_step n).
Proof.
intros n op Hvalid Hop.
unfold valid_input in *.
unfold collatz_step.
destruct op.
-
unfold valid_operation in Hop.
rewrite Hop.
assert (n >= 2).
{
destruct n; try lia.
destruct n; try lia.
unfold is_even in Hop.
simpl in Hop.
discriminate.
}
apply Nat.div_le_lower_bound; lia.
-
unfold valid_operation in Hop.
rewrite Hop.
lia.
Qed.



(* 序列有效性的归纳性质 *)
Lemma valid_sequence_inductive : forall n ops,
  valid_input n ->
  (forall i, i < length ops -> valid_operation (nth_sequence_value n i) (nth i ops R0)) ->
  forall k, k <= length ops ->
  valid_input (nth_sequence_value n k).
Proof.
intros n ops Hvalid Hseq k Hk.
induction k.
-
simpl. assumption.
-
simpl.
apply single_step_valid with (op := nth k ops R0).
+
apply IHk. lia.
+
apply Hseq. lia.
Qed.



(* 序列值的基本性质 *)
Lemma nth_sequence_value_0 : forall n,
  nth_sequence_value n 0 = n.
Proof.
intros n.
reflexivity.
Qed.

(* 序列值的递归性质 *)
Lemma nth_sequence_value_succ : forall n i,
  nth_sequence_value n (S i) = collatz_step (nth_sequence_value n i).
Proof.
intros n i.
reflexivity.
Qed.





 (* 序列有效性保持定理 *)
Theorem sequence_validity_preservation : forall n ops,
  valid_input n ->
  valid_sequence ops n ->
  valid_input (sequence_end n ops).
Proof.
intros n ops Hvalid Hseq.
unfold sequence_end.
apply valid_sequence_inductive with (ops := ops).
-
exact Hvalid.
-
intros i Hi.
apply Hseq.
exact Hi.
-
lia.
Qed.



(* 辅助引理：关于nth和firstn的关系 *)
Lemma nth_firstn_helper : forall {A: Type} (l: list A) (i n: nat) (default: A),
  i < n -> n <= length l ->
  nth i (firstn n l) default = nth i l default.
Proof.
intros A l i n default Hi Hn.
revert l i Hi Hn.
induction n as [|n' IHn'].
+
intros l i Hi Hn.
inversion Hi.
+
intros l i Hi Hn.
destruct l as [|x l'].
-
simpl in Hn. inversion Hn.
-
destruct i as [|i'].
*
simpl. reflexivity.
*
simpl.
apply IHn' with (l := l').
--
apply Nat.succ_lt_mono in Hi. exact Hi.
--
simpl in Hn. apply le_S_n. exact Hn.
Qed.

(* 序列前缀有效性引理 *)
Lemma sequence_prefix_validity : forall n ops i,
  valid_sequence ops n ->
  i <= length ops ->
  valid_sequence (firstn i ops) n.
Proof.
intros n ops i Hseq Hi j Hj.
rewrite firstn_length in Hj.
apply Nat.min_glb_lt_iff in Hj.
destruct Hj as [Hj_i Hj_len].
assert (Heq: nth j (firstn i ops) R0 = nth j ops R0).
{ apply nth_firstn_helper; auto. }
rewrite Heq.
apply Hseq.
apply Nat.lt_le_trans with i; auto.
Qed.



