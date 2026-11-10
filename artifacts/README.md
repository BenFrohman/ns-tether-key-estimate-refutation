# Certificate artifacts (version 1.1.0)

Author: Benjamin Stanley Frohman

These files are the Lean axiom output, the Lean build log, and the Arb
certificate result from the 10 November 2026 verification of
`ns-tether-key-estimate-refutation`. They do not change any mathematical
claim of the paper.

## Byte-identical `out/` logs

The six files in `out/` are byte-identical across:

- the local morning `./verify.sh` runs (`/tmp/nsrel-fresh-Q9Dj`,
  `/tmp/nsrel101-fresh-hebl`, `/tmp/nsrel102-fresh-JqFq`);
- `paper/axioms.txt` in the repository (same bytes as `out/axioms.log`);
- the GitHub Actions `verify-logs` artifacts of runs
  [42916652258](https://github.com/BenFrohman/ns-tether-key-estimate-refutation/actions/runs/42916652258)
  (pull request #1) and
  [42916649801](https://github.com/BenFrohman/ns-tether-key-estimate-refutation/actions/runs/42916649801)
  (push of `ci/rebuild-verify`).

SHA-256:

```
0f96cd25e33cd00a70e85307c5ee9befc626e4d8a6a81e2447cef11c7ce44825  out/axioms.log
5d5505e300911a4e62291ef3c5b76f402ca575b8c1d04936c6844fece3c47ab3  out/lake_build.log
659bbb570ac0bfab577ab1aa87c34ebbb96db3a505f1ffff1cadef38013b9727  out/v2_maxcert.log
f8b6611fccc794382df28e8eae925f1f201c8e1ac038509bcc3bdd06eb38f1df  out/v1_trig_example.log
9fb14bda19ba53e3635c93b2008219d47616f43c13a5eff119b81ada440df6be  out/v2_symbolic.log
542bfc3b4c74bf37819885886213e78b944428678accb4afed14efbabf388b4c  out/v2_sym.pkl
```

The certificate result log `out/v2_maxcert.log` ends with:

```
CERTIFIED: max |omega1|^2 = 144 attained only at the origin; M_1 = ||omega1||_inf = 12
```

## Verify transcripts (not byte-identical)

`local-verify/` holds full `./verify.sh` transcripts from the morning
runs. They all contain the CERTIFIED line above and `ALL CHECKS PASSED`.
They are not byte-identical to each other because the last line records
the local output directory and (in some copies) a `time(1)` footer.

`ci/` holds the GitHub Actions job logs for the two runs. Those logs
include runner timestamps and prefixes, so they are not byte-identical
to the local transcripts or to each other. The uploaded `verify-logs`
artifacts from those runs *are* byte-identical to `out/`.

## Toolchain

- Lean 4.22.0 (`leanprover/lean4:v4.22.0`, commit `ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05`)
- Mathlib `v4.22.0`, revision `79e94a093aff4a60fb1b1f92d9681e407124c2ca`
- Lean sources, scripts and `verify.sh` unchanged since commit
  `8fef153a12234ac28a311861c20df40e8d45e223` (included in tag `v1.0.0` at
  `ea9bbc0` and in release `v1.0.2`). The CI runs built `715626e`, which
  adds only `.github/workflows/verify.yml`.

One-command rebuild: `./verify.sh`
