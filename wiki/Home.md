# Collatz Conjecture Formalization

## Core Result

> **R0 Advantage Linear Growth Theorem**: For any positive integer m and iteration count t, the R0 (divide by 2) operation count advantage over R1 (3n+1) grows at least linearly: **R0 - R1 ≥ 2t**

This formalizes the core intuition: **division operations eventually dominate multiplication operations**.

---

## Project Scale

| Metric | Value |
|--------|-------|
| Core Theorems | 19 |
| Corollaries | 4 |
| Intermediate Results | 143 |
| Max Dependency Depth | 17 layers |
| Proof Files | 24 Coq files |

---

## Quick Navigation

| Page | Content |
|------|---------|
| [Core Insight](Core-Insight) | Qualitative understanding: why R0 wins |
| [Quantitative Results](Quantitative-Results) | Formulas, bounds, growth rates |
| [Theorem Roadmap](Theorem-Roadmap) | Dependency chain from foundations to global theorem |
| [Concepts & Notation](Concepts-Notation) | Symbol reference and glossary |
| [Interactive Visualization](cz_ms_cc_visualization) | Real-time Collatz sequence and chain structure visualization |

---

## The Collatz Problem

For any positive integer n:
- If n is even → n/2
- If n is odd → 3n+1

**Conjecture**: Every sequence eventually reaches 1.

### The Challenge

| Difficulty | Our Approach |
|------------|--------------|
| 2-adic × 3-adic mixing | Algebraic parameterization via entry functions |
| No global monotone function | R0 advantage theory |
| Chaotic sensitivity | Canonical chain decomposition |
| No modular obstruction | Mod 6 ≡ 2 orbit closure |
| "Almost all" ≠ "all" | Universal theorem for all positive integers |

---

## Key Innovation

**Entry Function Classification**:
```
Odd  m → valid_R1R0_entry_number(d,n) = 2·2^d·n + (2^d - 1)
Even m → valid_R0R0_entry_number(d,n) = n·2^d
```

Every positive integer has a unique (d, n) representation, transforming chaotic dynamics into structured algebraic analysis.

---

## Formal Verification

All theorems are machine-checked in **Coq**. The proof chain builds from basic definitions through intermediate lemmas to the global theorem.

See [Theorem Roadmap](Theorem-Roadmap) for the complete dependency structure.
