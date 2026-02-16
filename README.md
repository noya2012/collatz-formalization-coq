# Advancing the Collatz Conjecture: A Coq‑Formalized Proof of Linear Division Advantage on Structured Orbits

*Combinatorial Analysis and Machine Verification of the mod‑6≡2 Invariant*

*Author: JN.Z (JNZ)*

**License**: MIT License  
**Version**: 1.0  
**Last Updated**: January 2026  
**Contact**: For questions or contributions, please open an issue in the repository or contact the author through GitHub.

## Project Overview

This repository develops a comprehensive Coq formalization of the Collatz conjecture (3n+1 problem) using a **combinatorial analysis framework**. The approach identifies repeated patterns (R1R0 and R0R0 patterns) in Collatz sequences, constructs graph theory models, and combines local properties into global theorems, resulting in a complete proof system implemented in the Coq proof assistant.

**Key Breakthrough**: First rigorous formal proof that on the mod‑6≡2 orbit, the advantage of R0 operations (division by 2) over R1 operations (3n+1) grows at least linearly, providing core quantitative support for the convergence of Collatz sequences to 1.

The key technical contributions include:

1. **Canonical Representation Theory**: Parameterized (d,n) pairs establish one‑to‑one canonical representations, discretizing the continuous integer space via `valid_R1R0_entry_number(d,n)` and `valid_R0R0_entry_number(d,n)`

2. **Precise Quantification of R0 Advantage**: Proposes exact quantitative formulas:
   - R1R0 branch: r0s = d+1, r1s = d (advantage = 1)
   - R0R0 branch: r0s = d+1, r1s = 1 (advantage = d)

3. **mod‑6≡2 Orbit Invariant**: Systematically proves that mod‑6≡2 is an orbit invariant, constraining the infinite sequence space onto a structured sub‑orbit

4. **Macro‑step Iteration Design**: Defines macro‑step as a composite unit of R0R0 and R1R0 chains, converting complex single‑step analysis into modular structures

5. **Five‑Phase Progressive Proof Path**: Foundation building → Pattern analysis → Pattern transformation → R0 advantage theory → Global convergence

## Key Theorems and Breakthroughs

### Milestone Theorem System

#### 1. Complete Classification Theorem – `complete_number_classification` (collatz_part_3.v)
- Every natural number ≥1 can be uniquely classified as either an R1R0 or an R0R0 entry number
- Establishes the algebraic foundation of Collatz sequences

#### 2. Structural Control Theorem – `build_k_steps_structure` (collatz_part_6.v)
- k‑step expansion uses exactly k division‑by‑2 operations and at most k odd‑branch operations
- Sequence length is bounded above by 2k, creating an exact counting framework

#### 3. Canonical Numerical Bounds Theorem – `build_k_steps_numeric_canonical` (collatz_part_14.v)
- **The cornerstone of the whole system**, provides a unique canonical representation for every positive integer
- Delivers strict numerical constraints: $2\cdot3^d\cdot n \leq S < 2\cdot3^d\cdot(n+1)$
- Clearly identifies the operation pattern of canonical constructions

#### 4. mod‑6≡2 Orbit Macro‑step Theorem – `mod62_macrostep_iterated_lower_bound_canonical` (collatz_part_19.v)
- Proves that on the mod‑6≡2 orbit, each macro‑step yields a net advantage $\geq 2$
- The total contribution lower bound after $t$ macro‑step iterations is $2\cdot t$

#### 5. Global Advantage Growth Theorem – `global_mod62_advantage_growth_canonical` (collatz_part_19.v:811‑854)
- **The top‑level achievement and key breakthrough of the formalization**
- Six‑level nested existential quantifiers: $\exists(K,k,m_2,m_t,ops,chains)$
- Simultaneously constructs and constrains six objects satisfying eleven conditions
- Conclusion: For any input $m$ and iteration count $t$, there exists a construction satisfying all constraints, with an advantage lower bound of $2\cdot t$
- Depends on 143 preceding theorems, with a maximum depth of 17 layers

### R0 Advantage Theorem System Hierarchy
```
Level 6: Global layer – global_mod62_advantage_growth_canonical
    ↑
Level 5: Orbit layer – mod62_macrostep_iterated_lower_bound_canonical
    ↑
Level 4: Conversion layer – direct_conversion_to_mod6_2_orbit_canonical
    ↑
Level 3: Iterated chain layer – canonical_mod62_iterated_chains
    ↑
Level 2: Macrostep layer – canonical_mod62_macrostep_chains
    ↑
Level 1: Foundation layer – build_k_steps_numeric_canonical (Canonical Numerical Bounds Theorem)
    ↑
Base: Closed‑form lemmas + sub‑pattern derivations
```

## Proof Roadmap

| Part | Loads File | Focus | Distinct Results |
|------|------------|-------|------------------|
| `collatz_part_1.v` | `log2_p.v` | Core definitions: `CollatzOp`, `collatz_step`, sequence builders | Foundations of `build_k_steps` and counting helper functions |
| `collatz_part_2.v` | `collatz_part_1.v` | Parity algebra and basic number‑theory lemmas | `even_or_odd`, `even_div_pow2`, division by 2 preserves `valid_input` |
| `collatz_part_3.v` | `collatz_part_2.v` | Entry‑number characteristics of R1R0/R0R0 patterns | `complete_number_classification` plus induction principles for each entry |
| `collatz_part_4.v` | `collatz_part_3.v` | Sequence validity invariants | `sequence_validity_preservation`, prefix‑validity lemmas |
| `collatz_part_5.v` | `collatz_part_4.v` | Impact of appending `R0`/`R1R0` pairs on counts | `count_operations_app_R0`, `count_operations_app_R1R0`, `count_sum_c2` |
| `collatz_part_6.v` | `collatz_part_5.v` | Global structure of `build_k_steps` | `build_k_steps_structure`, `build_k_steps_increment_basic`, length bounds |
| `collatz_part_7.v` | `collatz_part_6.v` | Local two‑step behaviour | `R1R0_single_step`, `sequence_end_app`, `nth_sequence_value_app` |
| `collatz_part_8.v` | `collatz_part_7.v` | Closure of the R1R0 pattern loop | `sequence_end_two_steps`, `R1R0_pattern_closure` |
| `collatz_part_9.v` | `collatz_part_8.v` | Iteration of R1R0 blocks | `valid_R1R0_produces_R1R0_general`, `repeat_R1R0_output_even` |
| `collatz_part_10.v` | `collatz_part_9.v` | Symmetric analysis of R0 blocks | `valid_R0_produces_R0_general`, `repeat_R0_consecutive_count` |
| `collatz_part_11.v` | `collatz_part_10.v` | Pattern completeness and closed forms | `build_k_steps_pattern_completeness`, `repeat_R1R0_output_closed_form`, `R1R0_bounds_summary` |
| `collatz_part_12.v` | `collatz_part_11.v` | R0R0 bounds and combinatorial estimates | `R0R0_bounds_summary`, `build_k_steps_numeric_bounds_exists`, `build_k_steps_full_bounds` |
| `collatz_part_13.v` | `collatz_part_12.v` | Uniqueness of decompositions | `pow2_times_odd_unique`, `R1R0_decomposition_unique`, R0R0 uniqueness lemmas |
| `collatz_part_14.v` | `collatz_part_13.v` | Canonical classification with uniqueness and bounds | `complete_number_canonical_classification`, `build_k_steps_numeric_canonical` |
| `collatz_part_15.v` | `collatz_part_14.v` | Logarithmic depth control of canonical blocks | `canonical_d_log2_global`, `build_k_steps_numeric_canonical_length_log2` |
| `collatz_part_16.v` – `collatz_part_19.v` | Previous files | Canonical chains, macro‑step iteration, global advantage growth | `canonical_chain`, `mod62_macrostep_iterated_lower_bound_canonical`, `global_mod62_advantage_growth_canonical` |

**Exploration & Alternative Proof Files**:
- `collatz_part_6_1.v`: Extended structure theorems with existential quantifiers, `build_k_steps_length_min`, alternative proofs for `build_k_steps_structure`
- `collatz_part_16_1.v`: Deterministic pattern cycle theorem, `collatz_pattern_cycle_deterministic`, explores existential branching patterns
- `collatz_part_18_1.v`: Alternative chain record constructions, existential proof variants for macro-step analysis

**Extension files**:
- `log2_p.v`: Provides logarithmic facts
- `collatz_part_121.v`–`collatz_part_122.v`: Extend the library with monotonicity results using singular pattern combinations

## Project Structure

```
collatz/
├── collatz_part_1.v          # Core definitions and foundations
├── collatz_part_2.v          # Parity algebra and number theory
├── collatz_part_3.v          # Pattern classification
├── collatz_part_4.v          # Sequence validity
├── collatz_part_5.v          # Operation counting
├── collatz_part_6.v          # Global structure
├── collatz_part_7.v          # Local behaviour
├── collatz_part_8.v          # Pattern closure
├── collatz_part_9.v          # R1R0 block analysis
├── collatz_part_10.v         # R0 block analysis
├── collatz_part_11.v         # Pattern completeness
├── collatz_part_12.v         # Combinatorial bounds
├── collatz_part_13.v         # Uniqueness proofs
├── collatz_part_14.v         # Canonical classification
├── collatz_part_15.v         # Logarithmic bounds
├── collatz_part_16.v         # Canonical chain definitions
├── collatz_part_16_1.v       # Exploration: deterministic pattern cycle, existential proof variants
├── collatz_part_17.v         # Chain concatenation and advantage preservation
├── collatz_part_18.v         # Chain record structure
├── collatz_part_18_1.v       # Exploration: alternative chain constructions
├── collatz_part_19.v         # Macro‑step iteration and global advantage growth
├── collatz_part_6_1.v        # Exploration: extended structure theorems with existential quantifiers
├── collatz_part_121.v        # Extension: monotonicity 1
├── collatz_part_122.v        # Extension: monotonicity 2
├── log2_p.v                  # Logarithmic utilities
├── _CoqProject               # Coq project configuration
└── README.md                 # Original English documentation
```

## Quick Start

### Installation Requirements

**Dependencies:**
- **Coq Proof Assistant**: Version 8.10.2 or higher
- **OCaml**: Required for building Coq from source (optional if using pre-built binaries)
- **GNU Make**: Required for automated builds (optional on Windows)
- **Python 3.8+**: Required for dependency analysis tools (optional)

**Installation Options:**

1. **Using opam (Recommended)**:
```bash
opam install coq
```

2. **Using Docker**:
```bash
docker pull coqorg/coq
```

3. **Windows Binary**: Download from [Coq Release Page](https://github.com/coq/coq/releases)

### Build Instructions

Generate the makefile and build all targets:
```bash
coq_makefile -f _CoqProject -o Makefile
make
```

**Windows users**: If `make` is not available, invoke Coq directly:
```bash
# Compile main result
coqc collatz_part_19.v

# Compile all files in order
coqc log2_p.v
coqc collatz_part_1.v
# ... continue in dependency order
```

### Verification

To verify the formalization:

**1. Compile the main result:**
```bash
# Primary verification target
coqc collatz_part_19.v
```

**2. Run dependency analysis (optional):**
```bash
cd full_dependency_analysis
python dependency_extractor.py
python batch_dependency_extractor.py --verbose
```

**3. Generate lite code index (optional):**
```bash
cd full_dependency_analysis
python collatz_lite_generator.py
```

**4. Check dependency depth for key theorems:**
```bash
python major_theorem_dependency_analyzer.py global_mod62_advantage_growth_canonical --to-file
```

### Quick Reference
- Use `full_dependency_analysis/collatzlite.txt` for a proof‑free index of key definitions and statements, convenient for quick symbol lookup during proof work
- For details of key theorems, see the individual `.v` files and the methodology documents
- The dependency analysis reports are available in `full_dependency_analysis/theorems_dependence/`

## Key Contributions

This formalization establishes rigorous proofs of numerous local and global properties of Collatz sequences, including:

- **Main synthesis theorem**: Complete structural analysis of sequence patterns
- **Generating‑form theorem**: Mathematical characterization of pattern occurrences
- **Decomposition and composition theorems**: Operational properties of sequence operations
- **Upper‑bound theorems**: Precise numerical bounds on pattern behaviour
- **Pattern continuity and preservation**: Invariant properties during transformations

These contributions provide important insights into the dynamic and numerical‑optimization aspects of the Collatz conjecture, advancing the mathematical community's understanding of this challenging problem.

## Methodological Value

1. **Systematic approach**: A complete engineering system ranging from basic decomposition to global conclusions
2. **Precise quantification**: Pursuit of exact equalities and tight upper bounds, surpassing asymptotic descriptions
3. **Constructive existence**: All proofs come with explicit construction algorithms, supporting computable verification
4. **Modular composability**: Enables large‑scale formalization projects through lemma reuse

Building upon traditional Collatz research, this formalization supplies new analytical tools and proof paradigms to the field via formal verification methods. Not only does it prove key sub‑propositions of the Collatz conjecture, more importantly it **contributes a systematic technical framework to the domain of mathematical formalization**, demonstrating an effective path for transforming intuitive mathematical insights into machine‑verifiable proofs.

## Related Resources

- **Original research repository**: [noya2012/collatz-prof1](https://github.com/noya2012/collatz-prof1)
- **Coq proof assistant**: [https://coq.inria.fr/](https://coq.inria.fr/)
- **Collatz conjecture overview**: [Wikipedia](https://en.wikipedia.org/wiki/Collatz_conjecture)
- **Terence Tao's progress (2019)**: Almost all Collatz orbits attain almost bounded values

## Documentation

- **[Project Wiki](https://github.com/noya2012/collatz-formalization-coq/wiki)** - Interactive documentation with core insights, quantitative results, theorem roadmap, and concept reference

Additional documentation is available in the `docs/` directory:
- [Interactive Visualization](docs/cz_ms_cc_visualization.html) - Interactive visualization of Collatz sequence patterns and macro-step analysis
- [Theorem Descriptions](docs/theorem desc/) - Detailed documentation for 20+ key theorems and corollaries

## Changelog

### Version 1.0 (January 2026)
- Initial release of the comprehensive Coq formalization
- Core theorem system: 5 milestone theorems
- R0 Advantage Theorem System: 6-level hierarchical proof architecture
- Key breakthrough: `global_mod62_advantage_growth_canonical` theorem
- Dependency analysis framework with 7 Python tools
- Complete documentation in English and Chinese

### Key Statistics
- **Total theorems and corollaries**: 20+ main theorems
- **Maximum dependency depth**: 17 layers
- **Total Coq source files**: 19 core files + extensions
- **Lines of Coq code**: 10,000+ (excluding proofs)

---

*This formalization represents ongoing research into the Collatz conjecture through rigorous mathematical analysis and computer‑assisted proof verification.*