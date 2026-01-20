Load "collatz_part_10.v".


(* Pattern Completeness Theorem *)
Theorem build_k_steps_pattern_completeness : forall m,
	m >= 1 ->
	(exists d n, d >= 1 /\ n >= 0 /\ m = valid_R1R0_entry_number d n /\
							 build_k_steps m d = repeat_R1R0 d) \/
	(exists d n, d >= 1 /\ n >= 1 /\ m = valid_R0R0_entry_number d n /\
							 build_k_steps m d = repeat_R0 d).
Proof.
	intros m Hm.
	destruct (complete_number_classification m Hm) as [[Hodd [d [n [Hd [Hn HmR1R0]]]]] | [Heven [d [n [Hd [Hn HmR0R0]]]]]].
	- left.
		subst m. exists d, n. repeat split; try assumption.
		apply build_k_steps_on_valid_R1R0; assumption.
	- right.
		subst m. exists d, n. repeat split; try assumption.
		apply build_k_steps_on_valid_R0R0; assumption.
Qed.

(* R1R0 Sequence Final Value Exact Closed Form *)
Lemma repeat_R1R0_output_closed_form : forall D n,
	D >= 1 -> n >= 0 ->
	sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D)
		= 2 * (3^D * n + (3^D - 1) / 2).
Proof.
	intros D n HD Hn.
	pose proof (sequence_end_valid_R1R0_prefix D n D HD Hn (le_n _)) as Hp.
	simpl in Hp.
	rewrite Nat.sub_diag in Hp.
	rewrite valid_R1R0_entry_number_d0 in Hp.
	exact Hp.
Qed.


(* Multiple Property of 3^D minus 1 *)
Lemma pow3_minus1_twice_half : forall D,
	2 * ((3^D - 1) / 2) = 3^D - 1.
Proof.
	intro D.
	destruct (pow3_is_odd D) as [k Hk].
	rewrite Hk.
	replace ((2 * k + 1) - 1) with (2 * k) by lia.
	assert ((2 * k) / 2 = k) as ->.
	{ rewrite Nat.mul_comm. apply Nat.div_mul. lia. }
	lia.
Qed.

(* Corollary of R1R0 Final Value Closed Form *)
Corollary repeat_R1R0_output_closed_form_no_div : forall D n,
  D >= 1 -> n >= 0 ->
  sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) = 2 * 3^D * n + (3^D - 1).
Proof.
  intros D n HD Hn.
	rewrite (repeat_R1R0_output_closed_form D n HD Hn).
	rewrite Nat.mul_add_distr_l.
	rewrite pow3_minus1_twice_half.
	lia.
Qed.



(* R1R0 Final Value Upper Bound *)
Lemma repeat_R1R0_output_upper_bound : forall D n,
	D >= 1 -> n >= 0 ->
	sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) <= 3^D * (2 * n + 1).
Proof.
	intros D n HD Hn.
	rewrite (repeat_R1R0_output_closed_form_no_div D n HD Hn).
	replace (3 ^ D * (2 * n + 1)) with (2 * 3 ^ D * n + 3 ^ D) by ring.
	lia.
Qed.

(* R1R0 Final Value Linear Lower Bound: >= 2 * 3^D * n *)
Lemma repeat_R1R0_output_lower_bound_linear : forall D n,
	D >= 1 -> n >= 0 ->
	2 * 3^D * n <= sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D).
Proof.
	intros D n HD Hn.
	rewrite (repeat_R1R0_output_closed_form_no_div D n HD Hn).
	lia.
Qed.

(* R1R0 Final Value Constant Lower Bound: >= 3^D - 1 *)
Lemma repeat_R1R0_output_lower_bound_const : forall D n,
	D >= 1 -> n >= 0 ->
	3^D - 1 <= sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D).
Proof.
	intros D n HD Hn.
	rewrite (repeat_R1R0_output_closed_form_no_div D n HD Hn).
	lia.
Qed.

(* R1R0 Combined Bounds Summary: max(2*3^D*n, 3^D - 1) <= output <= 3^D*(2n+1) *)
Theorem R1R0_bounds_summary : forall D n,
	D >= 1 -> n >= 0 ->
	let out := sequence_end (valid_R1R0_entry_number D n) (repeat_R1R0 D) in
		(2 * 3^D * n <= out) /\ (3^D - 1 <= out) /\ out <= 3^D * (2*n + 1).
Proof.
	intros D n HD Hn out.
	split.
	- apply repeat_R1R0_output_lower_bound_linear; assumption.
	- split.
		+ apply repeat_R1R0_output_lower_bound_const; assumption.
		+ apply repeat_R1R0_output_upper_bound; assumption.
Qed.


(* Necessary and sufficient condition for R1R0 sequence output to be a power of 2 *)
Theorem R1R0_power_iff :
  forall d n k,
    d >= 1 -> n >= 0 ->
    (sequence_end (valid_R1R0_entry_number d n) (repeat_R1R0 d) = 2 ^ k) <->
    (2 ^ k + 1 = 3 ^ d * (2 * n + 1)).
Proof.
  intros d n k Hd Hn.
  assert (Hpow_ge1 : 1 <= 3 ^ d) by apply pow3_ge1.
  assert (Hsub_add : (3 ^ d - 1) + 1 = 3 ^ d) by lia.
  split; intro H.
  - (* -> direction *)
    pose proof (repeat_R1R0_output_closed_form_no_div d n Hd Hn) as Hclosed.
    rewrite Hclosed in H.
    symmetry in H.
    rewrite H.
    rewrite <- Nat.add_assoc.
    rewrite Hsub_add.
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_1_r.
    replace (3 ^ d * (2 * n)) with (2 * 3 ^ d * n) by
      (rewrite Nat.mul_assoc;
       rewrite (Nat.mul_comm (3 ^ d) 2);
       rewrite <- Nat.mul_assoc;
       reflexivity).
    reflexivity.
  - (* <- direction *)
    pose proof (repeat_R1R0_output_closed_form_no_div d n Hd Hn) as Hclosed.
    rewrite Nat.mul_add_distr_l in H.
    rewrite Nat.mul_1_r in H.
    replace (3 ^ d * (2 * n)) with (2 * 3 ^ d * n) in H by
      (rewrite Nat.mul_assoc;
       rewrite (Nat.mul_comm (3 ^ d) 2);
       rewrite <- Nat.mul_assoc;
       reflexivity).
    replace (2 * 3 ^ d * n + 3 ^ d) with (2 * 3 ^ d * n + ((3 ^ d - 1) + 1)) in H by
      (rewrite Hsub_add; reflexivity).
    rewrite Nat.add_assoc in H.
    rewrite Nat.add_1_r in H.
    rewrite Nat.add_1_r in H.
    apply Nat.succ_inj in H.
    rewrite Hclosed.
    symmetry.
    exact H.
Qed.


(* R1R0 sequence output modulo 6 equals 2 *)
Lemma R1R0_output_mod6 : forall d n, d >= 1 -> n >= 0 -> 
  sequence_end (valid_R1R0_entry_number d n) (repeat_R1R0 d) mod 6 = 2.
Proof.
  intros d n Hd Hn.
  rewrite repeat_R1R0_output_closed_form_no_div by lia.
  (* Prove that 3^d ≡ 3 mod 6 *)
  assert (H3d_mod: 3^d mod 6 = 3).
  { 
    destruct d as [|d].
    - lia.  (* The case d=0 is excluded by the precondition d>=1 *)
    - induction d as [|d IH].
      + simpl. lia.  (* The case d=1 *)
      + rewrite Nat.pow_succ_r by lia.
        rewrite Nat.mul_mod by lia.
        rewrite IH by lia.
        simpl. lia.
  }
  assert (H3d_minus1_mod : (3^d - 1) mod 6 = 2).
  {
    pose proof (Nat.div_mod (3 ^ d) 6) as Hdiv.
    specialize (Hdiv ltac:(lia)).
    rewrite H3d_mod in Hdiv.
    assert (Hdecomp : 3 ^ d - 1 = 6 * (3 ^ d / 6) + 2) by lia.
    rewrite Hdecomp.
    rewrite Nat.add_mod by lia.
    rewrite Nat.mul_comm.
    rewrite Nat.mod_mul by lia.
    simpl.
    reflexivity.
  }
  assert (Hmul_zero : 2 * 3 ^ d * n mod 6 = 0).
  {
    destruct d as [|d'].
    - lia.
    - rewrite Nat.pow_succ_r by lia.
      rewrite <- Nat.mul_assoc.
      rewrite <- Nat.mul_assoc with (n := 3) (m := 3 ^ d') (p := n).
      rewrite Nat.mul_assoc.
      replace (2 * 3) with 6 by lia.
      rewrite Nat.mul_comm with (n := 6) (m := 3 ^ d' * n).
      rewrite Nat.mod_mul by lia.
      reflexivity.
  }
  (* Direct modulo calculation: using basic arithmetic *)
  rewrite Nat.add_mod by lia.
  rewrite Hmul_zero.
  rewrite H3d_minus1_mod.
  simpl.
  reflexivity.
Qed.


(* R1R0 sequence output set is equivalent to numbers congruent to 2 mod 6 *)
Lemma R1R0_output_set_iff : forall m,
  (exists d n, d >= 1 /\ n >= 0 /\ m = sequence_end (valid_R1R0_entry_number d n) (repeat_R1R0 d)) <-> m mod 6 = 2.
Proof.
  split.
  - intros [d [n [Hd [Hn ->]]]]. apply R1R0_output_mod6; auto.
  - intros Hmod. exists 1, ((m-2)/6). split; [lia|split;[lia|]].
    rewrite repeat_R1R0_output_closed_form_no_div; try lia.
    replace (3^1) with 3 by auto.
    replace (2 * 3) with 6 by lia.
    replace (3 - 1) with 2 by lia.
    assert (Hdecomp : m = (m / 6) * 6 + 2).
    { pose proof (Nat.div_mod m 6) as Hdiv.
      specialize (Hdiv ltac:(lia)).
      rewrite Hmod in Hdiv.
      rewrite (Nat.mul_comm 6 (m / 6)) in Hdiv.
      exact Hdiv. }
    assert (Hminus : m - 2 = (m / 6) * 6) by lia.
    assert (Hdiv_eq : (m - 2) / 6 = m / 6).
    { rewrite Hminus.
      rewrite Nat.div_mul by lia.
      reflexivity. }
    rewrite Hdiv_eq.
    rewrite (Nat.mul_comm 6 (m / 6)).
    exact Hdecomp.
Qed.

