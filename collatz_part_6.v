Load "collatz_part_5.v".



(* “我们必须知道，我们必将知道。”（"Wir müssen wissen. Wir werden wissen."） *)
(*从这里我们根据前面得到的信息，开始全局证明
我们使用人工推导和机器推导的结合，利用本框架可靠的序列分解构造方法*)



(* 序列构造的性质 *)
Lemma build_k_steps_valid : forall n k,
  valid_input n ->
  valid_sequence (build_k_steps n k) n.
Proof.
intros n k Hvalid.
induction k as [|k' IHk].
-
simpl. unfold valid_sequence. intros. simpl in H. lia.
-
simpl build_k_steps.
remember (sequence_end n (build_k_steps n k')) as curr_n.
assert (Hvalid_curr : valid_input curr_n).
{ rewrite Heqcurr_n.
apply sequence_end_valid with (ops := build_k_steps n k').
- exact Hvalid.
- exact IHk. }
destruct (Nat.even curr_n) eqn:Heven.
+
assert (Hvalid_new: valid_sequence (build_k_steps n k' ++ [R0]) n).
{ unfold valid_sequence in *. intros i Hi.
rewrite app_length in Hi. simpl in Hi.
destruct (Nat.eq_dec i (length (build_k_steps n k'))) as [Heq|Hneq].
-
rewrite Heq.
unfold valid_operation.
assert (Hseq: curr_n = nth_sequence_value n (length (build_k_steps n k'))).
{ unfold sequence_end in Heqcurr_n.
exact Heqcurr_n. }
rewrite <- Hseq.
rewrite nth_append_last.
unfold is_even. exact Heven.
-
assert (i < length (build_k_steps n k')) by lia.
assert (nth i (build_k_steps n k' ++ [R0]) R0 = nth i (build_k_steps n k') R0).
{ rewrite app_nth1; auto. }
rewrite H0.
apply IHk.
exact H. }
exact Hvalid_new.
+
assert (Hvalid_new: valid_sequence (build_k_steps n k' ++ [R1; R0]) n).
{ unfold valid_sequence in *. intros i Hi.
rewrite app_length in Hi. simpl in Hi.
destruct (Nat.eq_dec i (length (build_k_steps n k'))) as [Heq1|Hneq1].
-
rewrite Heq1.
unfold valid_operation.
assert (Hseq: curr_n = nth_sequence_value n (length (build_k_steps n k'))).
{ unfold sequence_end in Heqcurr_n.
exact Heqcurr_n. }
rewrite <- Hseq.
pose proof (nth_append_two (build_k_steps n k') R1 R0) as [H1 H2].
rewrite H1.
unfold is_odd.
exact Heven.
- destruct (Nat.eq_dec i (S (length (build_k_steps n k')))) as [Heq2|Hneq2].
+
rewrite Heq2.
unfold valid_operation.
assert (Hodd: is_odd curr_n).
{ unfold is_odd. exact Heven. }
pose proof (nth_append_two (build_k_steps n k') R1 R0) as [H1 H2].
rewrite H2.
assert (Hstep: nth_sequence_value n (S (length (build_k_steps n k'))) = 3 * curr_n + 1).
{
rewrite nth_sequence_value_succ.
unfold collatz_step.
assert (Hseq: nth_sequence_value n (length (build_k_steps n k')) = curr_n).
{ symmetry. exact Heqcurr_n. }
rewrite Hseq.
rewrite Heven.
reflexivity.
}
rewrite Hstep.
unfold is_even.
apply even_3n_plus_1.
exact Hodd.
+
assert (i < length (build_k_steps n k')) by lia.
assert (nth i (build_k_steps n k' ++ [R1; R0]) R0 = nth i (build_k_steps n k') R0).
{ rewrite app_nth1; auto. }
rewrite H0.
apply IHk.
exact H. }
exact Hvalid_new.
Qed.


(* 关于序列构造的辅助引理 *)
Lemma build_k_steps_Sn : forall n k,
  valid_input n ->
  build_k_steps n (S k) =
  let prev_ops := build_k_steps n k in
  let curr_n := sequence_end n prev_ops in
  if Nat.even curr_n
  then prev_ops ++ [R0]
  else prev_ops ++ [R1; R0].
Proof.
intros n k Hvalid.
simpl. reflexivity.
Qed.

(* R1计数单调递增 *)
Lemma R1_count_monotone : forall n k,
  valid_input n ->
  let (_, r1s) := count_operations (build_k_steps n k) in
  let (_, r1s') := count_operations (build_k_steps n (S k)) in
  r1s' <= r1s + 1.
Proof.
intros n k Hvalid.
simpl build_k_steps.
destruct (count_operations (build_k_steps n k)) as [r0s r1s] eqn:Hcount.
destruct (Nat.even (sequence_end n (build_k_steps n k))) eqn:Heven.
-
destruct (count_operations (build_k_steps n k ++ [R0])) as [r0s' r1s'] eqn:Hcount'.
specialize (count_operations_app_R0 (build_k_steps n k)).
intros H_app.
rewrite Hcount in H_app.
rewrite Hcount' in H_app.
destruct H_app as [_ Heq].
rewrite Heq. lia.
-
destruct (count_operations (build_k_steps n k ++ [R1; R0])) as [r0s' r1s'] eqn:Hcount'.
specialize (count_operations_app_R1R0 (build_k_steps n k)).
intros H_app.
rewrite Hcount in H_app.
rewrite Hcount' in H_app.
destruct H_app as [_ Heq].
rewrite Heq. lia.
Qed.

(* 序列长度至少为k *)
Lemma build_k_steps_length_min : forall n k,
  valid_input n ->
  length (build_k_steps n k) >= k.
Proof.
induction k; intros Hvalid.
- simpl. lia.
- simpl build_k_steps.
remember (sequence_end n (build_k_steps n k)) as curr_n.
destruct (Nat.even curr_n).
+ rewrite app_length. simpl.
specialize (IHk Hvalid).
lia.
+ rewrite app_length. simpl.
specialize (IHk Hvalid).
lia.
Qed.

(* 序列长度至少为k 且最多为2k *)
Lemma build_k_steps_length_bound : forall n k,
  valid_input n ->
  k <= length (build_k_steps n k) <= 2 * k.
Proof.
induction k; intros Hvalid.
-
simpl. split; lia.
-
simpl build_k_steps.
remember (sequence_end n (build_k_steps n k)) as curr_n.
destruct (Nat.even curr_n).
+
rewrite app_length. simpl.
specialize (IHk Hvalid).
split.
*
lia.
*
lia.
+
rewrite app_length. simpl.
specialize (IHk Hvalid).
split.
*
lia.
*
lia.
Qed.

(* R0计数等于k *)
Lemma R0_count_eq_k : forall n k ops,
  valid_input n ->
  k >= 1 ->
  build_k_steps n k = ops ->
  let (r0s, _) := count_operations ops in
  r0s = k.
Proof.
intros n k ops Hvalid Hk Heq.
generalize dependent ops.
induction k as [|k' IHk].
-
intros ops Heq.
lia.
-
intros ops Heq.
simpl build_k_steps in Heq.
remember (sequence_end n (build_k_steps n k')) as curr_n.
assert (Hvalid_curr : valid_input curr_n).
{ rewrite Heqcurr_n.
apply sequence_end_valid with (ops := build_k_steps n k').
- exact Hvalid.
- apply build_k_steps_valid; auto. }
destruct (Nat.even curr_n) eqn:Heven.
+
rewrite <- Heq.
destruct k' as [|k''].
*
simpl.
destruct (count_operations (build_k_steps n 0)) as [r0s_old r1s_old].
destruct (count_operations (build_k_steps n 0 ++ [R0])) as [r0s_new r1s_new].
simpl in *.
reflexivity.
*
destruct (count_operations (build_k_steps n (S k''))) as [r0s_old r1s_old].
assert (H_prev: let (r0s, _) := count_operations (build_k_steps n (S k'')) in r0s = S k'').
{
apply IHk.
- lia.
- reflexivity.
}
destruct (count_operations (build_k_steps n (S k''))) as [r0s' r1s'] eqn:Heq_old.
destruct (count_operations (build_k_steps n (S k'') ++ [R0])) as [r0s_new r1s_new] eqn:Heq_new.
assert (r0s_new = S r0s').
{
pose proof (count_operations_app_R0 (build_k_steps n (S k''))) as H_count.
rewrite Heq_old in H_count.
rewrite Heq_new in H_count.
destruct H_count as [H_count _].
rewrite Nat.add_1_r in H_count.
exact H_count.
}
rewrite H.
rewrite H_prev.
reflexivity.
+
rewrite <- Heq.
destruct k' as [|k''].
*
simpl.
destruct (count_operations (build_k_steps n 0)) as [r0s_old r1s_old].
destruct (count_operations (build_k_steps n 0 ++ [R1; R0])) as [r0s_new r1s_new].
simpl in *.
reflexivity.
*
destruct (count_operations (build_k_steps n (S k''))) as [r0s_old r1s_old].
assert (H_prev: let (r0s, _) := count_operations (build_k_steps n (S k'')) in r0s = S k'').
{
apply IHk.
- lia.
- reflexivity.
}
destruct (count_operations (build_k_steps n (S k''))) as [r0s' r1s'] eqn:Heq_old.
destruct (count_operations (build_k_steps n (S k'') ++ [R1; R0])) as [r0s_new r1s_new] eqn:Heq_new.
assert (r0s_new = S r0s').
{
pose proof (count_operations_app_R1R0 (build_k_steps n (S k''))) as H_count.
rewrite Heq_old in H_count.
rewrite Heq_new in H_count.
destruct H_count as [H_count _].
exact H_count.
}
rewrite H.
rewrite H_prev.
reflexivity.
Qed.

(* 主定理：证明在k步序列中，R0操作次数恰好为k，则R1操作次数不超过k，且总长度不超过2k。
   这表明R0操作（n/2）在序列中占主导地位，支持了序列最终会收敛的直觉。 *)
Theorem build_k_steps_structure : forall n k,
  valid_input n ->
  k >= 2 ->
  exists ops r0s r1s,
  build_k_steps n k = ops /\
  count_operations ops = (r0s, r1s) /\
  r0s = k /\           (* 加强：R0的数量精确等于k *)
  r1s <= k /\          (* R1的数量最多为k *)
  r1s = length ops - k (* 新增：R1的精确值 *) /\
  length ops <= 2 * k. (* 总长度最多为2k *)
Proof.
intros n k Hvalid Hk.
assert (HR0: let (r0s, _) := count_operations (build_k_steps n k) in r0s = k).
{ apply (R0_count_eq_k n k (build_k_steps n k)).
- exact Hvalid.
- lia.
- reflexivity. }
assert (Hlen: length (build_k_steps n k) <= 2 * k).
{ apply build_k_steps_length_bound. assumption. }
assert (Hsum: let (r0s, r1s) := count_operations (build_k_steps n k) in
r0s + r1s = length (build_k_steps n k)).
{ apply count_sum_c2. }
destruct (count_operations (build_k_steps n k)) as [r0s r1s] eqn:Hcount.
exists (build_k_steps n k), r0s, r1s.
split; [reflexivity|].
split; [assumption|].
split.
-
rewrite HR0. reflexivity.
- split.
+
assert (r0s + r1s <= 2 * k).
{ rewrite Hsum. assumption. }
rewrite HR0 in H.
lia.
+ split.
*
rewrite <- Hsum.
rewrite HR0.
lia.
*
assumption.
Qed.

(* 动态性质的定理  所有合法k长度序列的结构证明了R0的增长是线性和可预测的
限制了R1的增长速率
支持了"R0操作在序列中占主导地位"的结论 *)

Theorem build_k_steps_increment_basic : forall n k,
  valid_input n ->
  k >= 2 ->
  let (r0s_k, r1s_k) := count_operations (build_k_steps n k) in
  let (r0s_next, r1s_next) := count_operations (build_k_steps n (S k)) in
  r0s_next = r0s_k + 1 /\                    (* R0精确增加1 *)
  r1s_next <= r1s_k + 1.                     (* R1最多增加1 *)
Proof.
intros n k Hvalid Hk.
destruct (build_k_steps_structure n k Hvalid Hk)
as [ops_k [r0s_k' [r1s_k' [Heq_k [Hcount_k [Hr0s_k [Hr1s_k _]]]]]]].
pose proof (build_k_steps_Sn n k Hvalid) as H_build.
rewrite Heq_k in H_build.
destruct (count_operations (build_k_steps n k)) as [r0s_k r1s_k] eqn:Hcount1.
destruct (count_operations (build_k_steps n (S k))) as [r0s_next r1s_next] eqn:Hcount2.
destruct (Nat.even (sequence_end n ops_k)) eqn:E.
-
split.
+
assert (H_chain: exists r0s_new r1s_new,
count_operations (ops_k ++ [R0]) = (r0s_new, r1s_new) /\
r0s_new = r0s_k + 1).
{
destruct (count_operations ops_k) as [r0s_old r1s_old] eqn:Hold.
exists (r0s_old + 1), r1s_old.
pose proof (count_operations_app_R0 ops_k) as H_count.
rewrite Hold in H_count.
rewrite Heq_k in Hcount1.
rewrite Hold in Hcount1.
injection Hcount1 as Hr0s_eq Hr1s_eq.
split.
-
destruct (count_operations (ops_k ++ [R0])) eqn:Hnew.
destruct H_count as [H_r0' H_r1'].
f_equal; auto.
-
rewrite Hr0s_eq.
reflexivity.
}
destruct H_chain as [r0s_new [r1s_new [H_new H_eq]]].
rewrite H_build in Hcount2.
simpl in Hcount2.
rewrite E in Hcount2.
rewrite H_new in Hcount2.
injection Hcount2 as H_next _.
rewrite <- H_next.
exact H_eq.
+
destruct (count_operations ops_k) as [r0s_old r1s_old] eqn:Hold.
rewrite Heq_k in Hcount1.
rewrite Hold in Hcount1.
injection Hcount1 as Hr0s_eq Hr1s_eq.
rewrite H_build in Hcount2.
simpl in Hcount2.
rewrite E in Hcount2.
pose proof (count_operations_app_R0 ops_k) as H_count.
rewrite Hold in H_count.
destruct (count_operations (ops_k ++ [R0])) eqn:Hnew.
destruct H_count as [_ H_r1].
injection Hcount2 as _ H_r1_next.
rewrite <- H_r1_next.
rewrite <- Hr1s_eq.
rewrite H_r1.
lia.
-
split.
+
assert (H_chain: exists r0s_new r1s_new,
count_operations (ops_k ++ [R1; R0]) = (r0s_new, r1s_new) /\
r0s_new = r0s_k + 1).
{
destruct (count_operations ops_k) as [r0s_old r1s_old] eqn:Hold.
exists (S r0s_old), (S r1s_old).
pose proof (count_operations_app_R1R0 ops_k) as H_count.
rewrite Hold in H_count.
rewrite Heq_k in Hcount1.
rewrite Hold in Hcount1.
injection Hcount1 as Hr0s_eq Hr1s_eq.
split.
-
destruct (count_operations (ops_k ++ [R1; R0])) eqn:Hnew.
destruct H_count as [H_r0' H_r1'].
f_equal.
+
exact H_r0'.
+
exact H_r1'.
-
rewrite Hr0s_eq.
lia.
}
destruct H_chain as [r0s_new [r1s_new [H_new H_eq]]].
rewrite H_build in Hcount2.
simpl in Hcount2.
rewrite E in Hcount2.
rewrite H_new in Hcount2.
injection Hcount2 as H_next _.
rewrite <- H_next.
exact H_eq.
+
destruct (count_operations ops_k) as [r0s_old r1s_old] eqn:Hold.
rewrite Heq_k in Hcount1.
rewrite Hold in Hcount1.
injection Hcount1 as Hr0s_eq Hr1s_eq.
rewrite H_build in Hcount2.
simpl in Hcount2.
rewrite E in Hcount2.
pose proof (count_operations_app_R1R0 ops_k) as H_count.
rewrite Hold in H_count.
destruct (count_operations (ops_k ++ [R1; R0])) eqn:Hnew.
destruct H_count as [_ H_r1].
injection Hcount2 as _ H_r1_next.
rewrite <- H_r1_next.
rewrite <- Hr1s_eq.
rewrite H_r1.
lia.
Qed.

