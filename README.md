# Collatz bounds Proof Library

This repository develops a staged Coq formalisation of a bounds view of the Collatz dynamics.  Each `collatz_part_*.v` file loads the previous one, growing a toolkit of parity lemmas, sequence combinators, counting arguments, and numeric bounds that culminate in macro-step theorems for odd inputs.  The companion `collatzlite.txt` offers a proof-free index of the key definitions and statements when you need a quick reminder of notation.

## Quick start
- Dependencies are declared in `_CoqProject`.  Generate a makefile and build all targets with:
  ```bash
  coq_makefile -f _CoqProject -o Makefile
  make
  ```
  On Windows without `make`, invoke Coq directly, e.g. `coqc collatz_part_15.v`.


## Proof roadmap (load order)
| Part | Loads | Focus | Featured results |
| --- | --- | --- | --- |
| `collatz_part_1.v` | `log2_p.v` | Core definitions: `CollatzOp`, `collatz_step`, sequence builders. | Foundations for `build_k_steps` and counting helpers. |
| `collatz_part_2.v` | `collatz_part_1.v` | Parity algebra and basic number theory lemmas. | `even_or_odd`, `even_div_pow2`, division-by-2 preserves `valid_input`. |
| `collatz_part_3.v` | `collatz_part_2.v` | Entry-number characterisations for R1R0 / R0R0 patterns. | `complete_number_classification` plus induction principles for each entry. |
| `collatz_part_4.v` | `collatz_part_3.v` | Sequence validity invariants. | `sequence_validity_preservation`, prefix validity lemmas. |
| `collatz_part_5.v` | `collatz_part_4.v` | Effect of appending `R0` / `R1R0` on counts. | `count_operations_app_R0`, `count_operations_app_R1R0`, `count_sum_c2`. |
| `collatz_part_6.v` | `collatz_part_5.v` | Global structure of `build_k_steps`. | `build_k_steps_structure`, `build_k_steps_increment_basic`, length bounds. |
| `collatz_part_7.v` | `collatz_part_6.v` | Local two-step behaviour. | `R1R0_single_step`, `sequence_end_app`, `nth_sequence_value_app`. |
| `collatz_part_8.v` | `collatz_part_7.v` | Closing the R1R0 pattern loop. | `sequence_end_two_steps`, `R1R0_pattern_closure`. |
| `collatz_part_9.v` | `collatz_part_8.v` | Iterated R1R0 blocks. | `valid_R1R0_produces_R1R0_general`, `repeat_R1R0_output_even`. |
| `collatz_part_10.v` | `collatz_part_9.v` | Symmetric analysis for R0 blocks. | `valid_R0_produces_R0_general`, `repeat_R0_consecutive_count`. |
| `collatz_part_11.v` | `collatz_part_10.v` | Pattern completeness and closed forms. | `build_k_steps_pattern_completeness`, `repeat_R1R0_output_closed_form`, `R1R0_bounds_summary`. |
| `collatz_part_12.v` | `collatz_part_11.v` | R0R0 bounds and combined estimates. | `R0R0_bounds_summary`, `build_k_steps_numeric_bounds_exists`, `build_k_steps_full_bounds`. |
| `collatz_part_13.v` | `collatz_part_12.v` | Uniqueness of decompositions. | `pow2_times_odd_unique`, `R1R0_decomposition_unique`, R0R0 uniqueness lemmas. |
| `collatz_part_14.v` | `collatz_part_13.v` | Canonical classification with uniqueness and bounds. | `complete_number_canonical_classification`, `build_k_steps_numeric_canonical`. |
| `collatz_part_15.v` | `collatz_part_14.v` | Logarithmic depth control for canonical blocks. | `canonical_d_log2_global`, `build_k_steps_numeric_canonical_length_log2`. |


The auxiliary `log2_p.v` supplies logarithm facts, while `collatz_part_121.v`–`collatz_part_123.v` extend the library with monotonicity results for more exotic pattern compositions.

## Milestone theorems
- **Complete classification**: `complete_number_classification` (Part 3) splits every natural number ≥1 into exactly one R1R0 or R0R0 entry with explicit parameters.
- **Structural control**: `build_k_steps_structure` (Part 6) shows every `k`-step expansion uses exactly `k` halving steps and at most `k` odd branches, capping length at `2k`.
- **Pattern completeness & bounds**: `build_k_steps_pattern_completeness` (Part 11) identifies the exact repeating pattern selected by `build_k_steps`, while `R1R0_bounds_summary` and `R0R0_bounds_summary` (Parts 11–12) pin down the numeric range of outputs.
- **Canonical representation**: `build_k_steps_numeric_canonical` (Part 14) gives uniqueness and quantitative bounds for the canonical branch of any input, and Part 15 upgrades this with the logarithmic bound `build_k_steps_numeric_canonical_length_log2`.

### Spotlight: `build_k_steps_numeric_canonical`

This theorem is the keystone of the development.  It says that every integer `m ≥ 1` chooses a *unique* canonical branch: either an odd-entry macro step (`repeat_R1R0`) with tight lower/upper bounds on the resulting value, or an even-entry macro step (`repeat_R0`) that collapses exactly back to its seed.  Moreover, the statement internalises the uniqueness proofs, so any competing `d', n'` parameters must coincide with the canonical pair.  Together with the logarithmic depth lemmas of Part 15, it ties the earlier structural work (Parts 6–11) to concrete numeric control, making it the strongest global classification result in the library.


For quick reference during proof work, use `collatzlite.txt`—it mirrors the definition order above without proof scripts, so you can locate theorems fast while editing the full development.
