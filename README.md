Lean formalization of Section 4 of
[*Finding Colorings in One-Sided Expanders*](https://arxiv.org/abs/2508.02825),
by Rares-Darius Buhai, Yiding Hua, David Steurer, and Andor Vári-Kakas.

The formalization was produced by GPT-5.1 under the prompting and supervision
of Rares-Darius Buhai. Detailed scope and provenance are recorded in
[`formalization.yaml`](formalization.yaml).

The Lean formalization and repository code are licensed under the
[Apache License 2.0](LICENSE). The source paper is distributed separately under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

## Comparator challenge

The repository exposes a trusted `Challenge` module and a proved `Solution`
module for [leanprover/comparator](https://github.com/leanprover/comparator).
The checked declarations are:

- `ThresholdRank.large_bottom_rank_implies_large_top_rank`
- `ThresholdRank.small_top_rank_implies_small_bottom_rank`

Build the trusted formalization, challenge, and pinned tools with:

```sh
lake build
lake build comparator lean4export
```

Lean, Mathlib, and `lean4export` are pinned to `v4.27.0-rc1`. Comparator is
pinned to a Lean 4.27-compatible follow-up commit that adds its hardened
filesystem and executable allowlist. Keep Comparator and `lean4export`
together: their export format is version-sensitive.

Comparator's sandboxing requires Linux and a genuine
[`landrun`](https://github.com/Zouuup/landrun) in `PATH`. The hardened
invocation below also uses `systemd-run`. From a clean, trusted checkout, run:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env .lake/packages/Comparator/.lake/build/bin/comparator comparator.json'
```

The pinned Comparator revision expects executables named `landrun` and
`lean4export` in `PATH`; `lake env` supplies the latter from the pinned Lake
dependency.

`Challenge.lean` imports only upstream Mathlib and defines the two threshold
ranks locally; it has no dependency on the proof implementation under
`Colorexpanders`. The challenge, `comparator.json`, the toolchain and Lake
configuration, Mathlib, and the checker binaries/caches form the trusted
boundary. Do not compile an untrusted replacement `Solution.lean` outside
Comparator's sandbox in the same checkout.
