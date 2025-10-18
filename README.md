# Collatz Conjecture Combinatorial Analysis Framework - Coq Formalization

This repository develops a comprehensive Coq formalization of the Collatz conjecture (3n+1 problem) using combinatorial analysis methods. The project constructs a staged proof library that establishes local and global properties of Collatz sequences through rigorous mathematical formalization.

## Table of Contents
- [Project Background](#project-background)
- [Technical Approach](#technical-approach)
- [Quick Start](#quick-start)
- [Proof Roadmap](#proof-roadmap)
- [Milestone Theorems](#milestone-theorems)
- [Project Structure](#project-structure)
- [Key Contributions](#key-contributions)
- [Related Resources](#related-resources)

## Project Background

The Collatz Conjecture, also known as the Hailstone Conjecture, is an unsolved mathematical problem that has challenged mathematicians since its proposal by Lothar Collatz in the 1930s. Despite its simple statement—*for any positive integer n, repeatedly applying the rule: if n is even, divide it by 2; if it is odd, multiply it by 3 and add 1, eventually reaches 1*—the conjecture has proven exceptionally difficult to prove or disprove.

**Key Challenges:**
- **Simplicity vs. Complexity**: The problem statement is extremely simple, but its proof has eluded mathematicians for over 60 years
- **Computational Verification Limits**: While computers have verified all positive integers less than 2^68 (approximately 2.9 × 10^20) conform to the conjecture, this is insufficient for general proof
- **Dynamical System Behavior**: The complex behavior of the underlying dynamical system makes the conjecture exceptionally challenging

**Historical Context:**
Paul Erdős famously stated, *"Mathematics is not yet ready to handle such a problem,"* offering a $500 prize in 1983 for its proof or disproof. In 2019, Terence Tao made significant progress by proving that almost all (99.99% or more) starting values eventually reach values below 200.

## Technical Approach

This project adopts a **combinatorial analysis framework** that transforms the problem from individual number verification to structural pattern analysis. Our methodology involves:

1. **Pattern Recognition**: Identifying recurring patterns in Collatz sequences (R1R0 and R0R0 patterns)
2. **Graph-Theoretic Analysis**: Combining local properties into triangular undirected graphs
3. **Graph Decomposition**: Re-decomposing graphs to obtain sequence property theorems
4. **Formal Verification**: Implementing all proofs in the Coq proof assistant for mathematical rigor

**Key Innovations:**
- **Macro-step Analysis**: Instead of tracking individual steps, we analyze blocks of operations
- **Canonical Classification**: Every natural number ≥1 can be uniquely classified into specific pattern categories
- **Numeric Bounds**: Establishing concrete upper and lower bounds for sequence behaviors
- **Logarithmic Depth Control**: Proving that canonical branches have logarithmic complexity

## Quick Start

### Dependencies
The project requires Coq proof assistant. Dependencies are declared in `_CoqProject`.

### Build Instructions
Generate a makefile and build all targets:
```bash
coq_makefile -f _CoqProject -o Makefile
make
```

**Windows Users**: Without `make`, invoke Coq directly:
```bash
coqc collatz_part_15.v
```

### Quick Reference
Use `collatzlite.txt` for a proof-free index of key definitions and statements when you need quick notation reminders during proof work.

## Proof Roadmap

Each `collatz_part_*.v` file loads the previous one, building a comprehensive toolkit of parity lemmas, sequence combinators, counting arguments, and numeric bounds that culminate in macro-step theorems for odd inputs.

| Part | Loads | Focus | Featured Results |
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

**Extension Files:**
- `log2_p.v`: Supplies logarithm facts
- `collatz_part_121.v`–`collatz_part_123.v`: Extend the library with monotonicity results for exotic pattern compositions

## Milestone Theorems

### Complete Classification
**`complete_number_classification`** (Part 3) splits every natural number ≥1 into exactly one R1R0 or R0R0 entry with explicit parameters.

### Structural Control
**`build_k_steps_structure`** (Part 6) shows every `k`-step expansion uses exactly `k` halving steps and at most `k` odd branches, capping length at `2k`.

### Pattern Completeness & Bounds
**`build_k_steps_pattern_completeness`** (Part 11) identifies the exact repeating pattern selected by `build_k_steps`, while `R1R0_bounds_summary` and `R0R0_bounds_summary` (Parts 11–12) pin down the numeric range of outputs.

### Canonical Representation
**`build_k_steps_numeric_canonical`** (Part 14) gives uniqueness and quantitative bounds for the canonical branch of any input, and Part 15 upgrades this with the logarithmic bound `build_k_steps_numeric_canonical_length_log2`.

### Spotlight: `build_k_steps_numeric_canonical`
This theorem is the **keystone** of the development. It states that every integer `m ≥ 1` chooses a *unique* canonical branch: either an odd-entry macro step (`repeat_R1R0`) with tight lower/upper bounds on the resulting value, or an even-entry macro step (`repeat_R0`) that collapses exactly back to its seed. The statement internalizes uniqueness proofs—any competing `d', n'` parameters must coincide with the canonical pair. Together with logarithmic depth lemmas, it connects structural work to concrete numeric control, representing the strongest global classification result in the library.

## Project Structure

```
collatz/
├── collatz_part_1.v          # Core definitions and foundations
├── collatz_part_2.v          # Parity algebra and number theory
├── collatz_part_3.v          # Pattern classification
├── collatz_part_4.v          # Sequence validity
├── collatz_part_5.v          # Operation counting
├── collatz_part_6.v          # Global structure
├── collatz_part_7.v          # Local behavior
├── collatz_part_8.v          # Pattern closure
├── collatz_part_9.v          # R1R0 block analysis
├── collatz_part_10.v         # R0 block analysis
├── collatz_part_11.v         # Pattern completeness
├── collatz_part_12.v         # Combined bounds
├── collatz_part_13.v         # Uniqueness proofs
├── collatz_part_14.v         # Canonical classification
├── collatz_part_15.v         # Logarithmic bounds
├── collatz_part_121.v        # Extension: Monotonicity 1
├── collatz_part_122.v        # Extension: Monotonicity 2
├── collatz_part_123.v        # Extension: Monotonicity 3
├── log2_p.v                  # Logarithm utilities
├── collatzlite.txt           # Quick reference guide
├── _CoqProject               # Coq project configuration
└── README.md                 # This file
```

## Key Contributions

This formalization establishes **dozens of local and global properties** of Collatz sequences, including:

- **Main Composition Theorem**: Complete structural analysis of sequence patterns
- **Generation Form Theorems**: Mathematical characterization of pattern emergence
- **Decomposition & Combination Theorems**: Operational properties of sequence manipulation
- **Upper Bound Theorems**: Exact numerical bounds for pattern behaviors
- **Pattern Continuity & Preservation**: Invariant properties across transformations


These contributions provide significant insights into the dynamics and numerical optimization aspects of the Collatz conjecture, advancing the mathematical community's understanding of this challenging problem.

## Related Resources

- **Original Research Repository**: [noya2012/collatz-prof1](https://github.com/noya2012/collatz-prof1)
- **Coq Proof Assistant**: [https://coq.inria.fr/](https://coq.inria.fr/)
- **Collatz Conjecture Overview**: [Wikipedia](https://en.wikipedia.org/wiki/Collatz_conjecture)
- **Terence Tao's Progress (2019)**: Almost all Collatz orbits attain almost bounded values

---

*This formalization represents ongoing research into the Collatz conjecture through rigorous mathematical analysis and computer-assisted proof verification.*