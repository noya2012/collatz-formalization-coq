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