(* 兼容 Coq 8.10.2： *)
Load "collatz_part_121.v".

(* 严格单调性定理：repeat_R0输出关于n严格递增 *)
Theorem repeat_R0_output_strict_mono : forall D n n',
  D >= 1 -> n >= 1 -> n' >= 1 -> n < n' ->
  sequence_end (valid_R0R0_entry_number D n) (repeat_R0 D) <
  sequence_end (valid_R0R0_entry_number D n') (repeat_R0 D).
Proof.
intros D n n' HD Hn Hn' Hlt.
rewrite (repeat_R0_output_reaches_one D n HD Hn).
rewrite (repeat_R0_output_reaches_one D n' HD Hn').
exact Hlt.
Qed.

(* 单射性：对于固定 D，输出相等推出 n 相等 *)
Corollary repeat_R0_output_injective_in_n : forall D n n',
  D >= 1 -> n >= 1 -> n' >= 1 ->
  sequence_end (valid_R0R0_entry_number D n) (repeat_R0 D) =
  sequence_end (valid_R0R0_entry_number D n') (repeat_R0 D) ->
  n = n'.
Proof.
intros D n n' HD Hn Hn' Heq.
rewrite (repeat_R0_output_reaches_one D n HD Hn) in Heq.
rewrite (repeat_R0_output_reaches_one D n' HD Hn') in Heq.
exact Heq.
Qed.

(* =============== 增量（差分）形式辅助定理 =============== *)
(* 单步差分：由于 R0R0 模式的终值就是 n 本身，单步差分直接等于 n 的差值 *)
Lemma repeat_R0_output_step_delta : forall D n,
  D >= 1 -> n >= 1 ->
  sequence_end (valid_R0R0_entry_number D (S n)) (repeat_R0 D)
    = sequence_end (valid_R0R0_entry_number D n) (repeat_R0 D) + 1.
Proof.
intros D n HD Hn.
rewrite (repeat_R0_output_reaches_one D (S n) HD).
2:{ lia. }
rewrite (repeat_R0_output_reaches_one D n HD Hn).
simpl.
lia.
Qed.

(* 广义差分：对所有 n <= n', 输出差值 = n' - n *)
Lemma repeat_R0_output_linear_increment : forall D n n',
  D >= 1 -> n >= 1 -> n' >= n ->
  sequence_end (valid_R0R0_entry_number D n') (repeat_R0 D)
    = sequence_end (valid_R0R0_entry_number D n) (repeat_R0 D)
      + (n' - n).
Proof.
intros D n n' HD Hn Hle.
rewrite (repeat_R0_output_reaches_one D n' HD).
2:{ lia. }
rewrite (repeat_R0_output_reaches_one D n HD Hn).
replace n' with (n + (n' - n)) at 1 by lia.
lia.
Qed.

(* 单步严格递增作为差分推论 *)
Corollary repeat_R0_output_step_strict_increase : forall D n,
  D >= 1 -> n >= 1 ->
  sequence_end (valid_R0R0_entry_number D n) (repeat_R0 D) <
  sequence_end (valid_R0R0_entry_number D (S n)) (repeat_R0 D).
Proof.
intros D n HD Hn.
rewrite (repeat_R0_output_step_delta D n HD Hn).
assert (1 > 0) by lia.
lia.
Qed.

(* 从差分形式快速得到严格单调——与已证明的 strict_mono 等价 *)
Corollary repeat_R0_output_strict_mono_alt : forall D n n',
  D >= 1 -> n >= 1 -> n' >= 1 -> n < n' ->
  sequence_end (valid_R0R0_entry_number D n) (repeat_R0 D) <
  sequence_end (valid_R0R0_entry_number D n') (repeat_R0 D).
Proof.
intros D n n' HD Hn Hn' Hlt.
assert (Hle: n' >= n) by lia.
rewrite (repeat_R0_output_linear_increment D n n' HD Hn Hle).
assert ((n' - n) > 0).
{ apply sub_pos_strict; lia. }
lia.
Qed.

(* Injectivity 也可由差分形式直接给出（替代前面证明） *)
Corollary repeat_R0_output_injective_in_n_alt : forall D n n',
  D >= 1 -> n >= 1 -> n' >= 1 ->
  sequence_end (valid_R0R0_entry_number D n) (repeat_R0 D) =
  sequence_end (valid_R0R0_entry_number D n') (repeat_R0 D) ->
  n = n'.
Proof.
intros D n n' HD Hn Hn' Heq.
destruct (Nat.lt_trichotomy n n') as [Hlt|[Heq'|Hgt]]; try lia.
-
pose proof (repeat_R0_output_strict_mono_alt D n n' HD Hn Hn' Hlt) as HltOut.
rewrite Heq in HltOut; lia.
-
pose proof (repeat_R0_output_strict_mono_alt D n' n HD Hn' Hn Hgt) as HltOut.
rewrite <- Heq in HltOut; lia.
Qed.

