(* 兼容 Coq 8.10.2： *)
Load "collatz_part_11.v".

(* 严格单调性定理：repeat_R1R0输出关于n严格递增 *)
Theorem repeat_R1R0_output_strict_mono : forall D n n',
  D >= 1 -> n >= 0 -> n' >= 0 -> n < n' ->
  sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) <
  sequence_end (valid_R1R0_entry_number D n') (repeat_R1R0 D).
Proof.
intros D n n' HD Hn Hn' Hlt.
rewrite (repeat_R1R0_output_closed_form_no_div D n HD Hn).
rewrite (repeat_R1R0_output_closed_form_no_div D n' HD Hn').
assert (Hpow_pos: 0 < 3 ^ D) by apply pow3_pos.
assert (Hfac_pos: 0 < 2 * 3 ^ D) by (apply mul_pos_pos_nat; lia || apply pow3_pos).
assert (Hdelta: n' - n > 0) by (apply sub_pos_strict; lia).
replace n' with (n + (n' - n)) at 2 by lia.
replace (2 * 3 ^ D * (n + (n' - n))) with
(2 * 3 ^ D * n + 2 * 3 ^ D * (n' - n)) by (rewrite Nat.mul_add_distr_l; lia).
assert (Htail: 0 < 2 * 3 ^ D * (n' - n)).
{ apply mul_pos_pos_nat.
- apply mul_pos_pos_nat; [lia|apply pow3_pos].
- apply sub_pos_strict; lia.
}
lia.
Qed.

(* 单射性：对于固定 D，输出相等推出 n 相等 *)
Corollary repeat_R1R0_output_injective_in_n : forall D n n',
  D >= 1 -> n >= 0 -> n' >= 0 ->
  sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) =
  sequence_end (valid_R1R0_entry_number D n') (repeat_R1R0 D) ->
  n = n'.
Proof.
intros D n n' HD Hn Hn' Heq.
destruct (Nat.lt_trichotomy n n') as [Hlt | [Heq' | Hgt]].
- pose proof (repeat_R1R0_output_strict_mono D n n' HD Hn Hn' Hlt) as Hmono.
rewrite Heq in Hmono. lia.
- exact Heq'.
- pose proof (repeat_R1R0_output_strict_mono D n' n HD Hn' Hn Hgt) as Hmono.
rewrite <- Heq in Hmono. lia.
Qed.

(* =============== 增量（差分）形式辅助定理 =============== *)
(* 单步闭式差分：输出对 n 的线性增量步长是常数 2 * 3^D *)
Lemma repeat_R1R0_output_step_delta : forall D n,
  D >= 1 -> n >= 0 ->
  sequence_end (valid_R1R0_entry_number D (S n)) (repeat_R1R0 D)
    = sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) + 2 * 3 ^ D.
Proof.
intros D n HD Hn.
rewrite (repeat_R1R0_output_closed_form_no_div D (S n) HD).
2:{ lia. }
rewrite (repeat_R1R0_output_closed_form_no_div D n HD Hn).
simpl.
replace (2 * 3 ^ D * S n) with (2 * 3 ^ D * n + 2 * 3 ^ D) by lia.
lia.
Qed.

(* 广义差分：对所有 n <= n', 输出差值 = 2 * 3^D * (n' - n) *)
Lemma repeat_R1R0_output_linear_increment : forall D n n',
  D >= 1 -> n >= 0 -> n' >= n ->
  sequence_end (valid_R1R0_entry_number D n') (repeat_R1R0 D)
    = sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D)
      + 2 * 3 ^ D * (n' - n).
Proof.
intros D n n' HD Hn Hle.
rewrite (repeat_R1R0_output_closed_form_no_div D n' HD).
2:{ lia. }
rewrite (repeat_R1R0_output_closed_form_no_div D n HD Hn).
replace n' with (n + (n' - n)) at 1 by lia.
rewrite Nat.mul_add_distr_l.
lia.
Qed.

(* 单步严格递增作为差分推论（可避免重新展开闭式） *)
Corollary repeat_R1R0_output_step_strict_increase : forall D n,
  D >= 1 -> n >= 0 ->
  sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) <
  sequence_end (valid_R1R0_entry_number D (S n)) (repeat_R1R0 D).
Proof.
intros D n HD Hn.
rewrite (repeat_R1R0_output_step_delta D n HD Hn).
assert (2 * 3 ^ D > 0) by (apply mul_pos_pos_nat; lia || apply pow3_pos).
lia.
Qed.

(* 从差分形式快速得到严格单调——与已证明的 strict_mono 等价 *)
Corollary repeat_R1R0_output_strict_mono_alt : forall D n n',
  D >= 1 -> n >= 0 -> n' >= 0 -> n < n' ->
  sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) <
  sequence_end (valid_R1R0_entry_number D n') (repeat_R1R0 D).
Proof.
intros D n n' HD Hn Hn' Hlt.
assert (Hle: n' >= n) by lia.
rewrite (repeat_R1R0_output_linear_increment D n n' HD Hn Hle).
assert (2 * 3 ^ D * (n' - n) > 0).
{ apply mul_pos_pos_nat.
- apply mul_pos_pos_nat; lia || apply pow3_pos.
- apply sub_pos_strict; lia.
}
lia.
Qed.

(* Injectivity 也可由差分形式直接给出（替代前面证明） *)
Corollary repeat_R1R0_output_injective_in_n_alt : forall D n n',
  D >= 1 -> n >= 0 -> n' >= 0 ->
  sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) =
  sequence_end (valid_R1R0_entry_number D n') (repeat_R1R0 D) ->
  n = n'.
Proof.
intros D n n' HD Hn Hn' Heq.
destruct (Nat.lt_trichotomy n n') as [Hlt|[Heq'|Hgt]]; try lia.
-
pose proof (repeat_R1R0_output_strict_mono_alt D n n' HD Hn Hn' Hlt) as HltOut.
rewrite Heq in HltOut; lia.
-
pose proof (repeat_R1R0_output_strict_mono_alt D n' n HD Hn' Hn Hgt) as HltOut.
rewrite <- Heq in HltOut; lia.
Qed.