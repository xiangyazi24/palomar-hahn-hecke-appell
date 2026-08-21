# Contributing

This repository is a fixed, self-contained Palomar snapshot of one formalized
paper. Changes should preserve the exact correspondence among the manuscript,
`Challenge.lean`, `Solution.lean`, `comparator.json`, and the 19-file extracted
proof closure.

Before opening a pull request:

1. Explain which paper claim or formal statement changes and why.
2. Keep the two registered declarations statement-identical between
   `Challenge.lean` and `Solution.lean`.
3. Do not add proof `sorry`, custom axioms, `unsafe`, or answer-bearing data to
   the Challenge.
4. Run the verification commands in `README.md`, including the pinned
   Comparator check.
5. Rebuild the PDF when its TeX source changes and report the exact commit that
   was checked.

For provenance corrections or security concerns, open a GitHub issue without
including private repository material or credentials.
