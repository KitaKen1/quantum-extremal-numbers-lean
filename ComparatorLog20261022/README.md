# Public Comparator verification evidence (2026-10-22)

[Public GitHub Actions run](https://github.com/KitaKen1/quantum-extremal-numbers-lean/actions/runs/39714466024) — **PASS**.

- Tested verification-kit commit: `0ff64b704b2532acaae014166a6d8d6f44057587`.
- Original proof commit: `7d7e3afdadabdb2fa964cea99711d05fc5652022`.
- PR statement snapshot: `3ea4821704dfde365879d6a2d6f2f58e8f8d54e9`.
- Lean: `leanprover/lean4:v4.33.1`.

All three targets passed statement/definition comparison, transitive axiom checks
and Lean kernel acceptance in the pinned Comparator. The original 20-theorem
axiom audit, FC statement compilation, full-environment `leanchecker --fresh Solution`
replay and all diagnostic controls also passed. Allowed axioms are `propext`,
`Classical.choice` and `Quot.sound`. This is an author-controlled public CI run;
it does not constitute an independent third-party review.

The artifact ZIP was downloaded after the workflow completed. All
20 SHA-256 entries in `receipts/result.json` were
verified locally, along with the checked repository/proof commits and tool pins.
The original artifact ZIP hash is preserved in `PUBLIC_CI_RESULT.json`.

The evidence is committed here for durability beyond GitHub artifact retention.
`receipts/comparator.log` records the selected-target replay; the separate
`receipts/fresh-replay-time.log` records the full-environment replay with exit 0.
An empty `receipts/fresh-replay.log` is expected on success.

Measured public-run wall times: total job 2300 seconds; Comparator
including the proof build 234.305 seconds; full-environment fresh replay
1817.24 seconds. The public runner had about 15 GiB RAM and 95 GiB
available disk after dependency retrieval; fresh replay peaked at about 10 GiB RSS.

Reproduction instructions: [`../leanWithComparator/README.md`](../leanWithComparator/README.md).
This directory records a completed run at the exact tested commit above; it is
added in a later documentation/evidence commit without changing any verified input.
