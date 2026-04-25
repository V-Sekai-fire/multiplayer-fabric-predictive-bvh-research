# multiplayer-fabric-predictive-bvh-research

Aspirational / research-tier Lean 4 proofs split out of
[multiplayer-fabric-predictive-bvh](https://github.com/V-Sekai-fire/multiplayer-fabric-predictive-bvh).

## Why a separate repo

The production-tier `predictive-bvh` repo emits `predictive_bvh.h`, the C
header consumed by the production engine. Its `lake build` (default target =
`bvh-codegen` exe) is the production gate.

The modules in **this** repo encode model-level claims that are not in the
codegen import closure — abstract BVH query soundness, zone migration protocol
correctness, ReBAC authorisation bounds, etc. They are valuable as research
artefacts, but they don't gate the bytes that ship.

Several of them are currently broken under Lean 4.26 (proof rot from toolchain
upgrades, deprecated syntax). Hosting them here keeps the production repo's CI
green while preserving the work for incremental repair.

## Layout

| Path | Status | Source |
|---|---|---|
| `PredictiveBVHResearch/Spatial/Partition.lean` | broken | `PredictiveBVH/Spatial/Partition.lean` |
| `PredictiveBVHResearch/Spatial/Tree.lean` | broken | `PredictiveBVH/Spatial/Tree.lean` |
| `PredictiveBVHResearch/Spatial/RefitIncremental.lean` | broken (depends on Tree) | `PredictiveBVH/Spatial/RefitIncremental.lean` |
| `PredictiveBVHResearch/Protocol/Build.lean` | broken | `PredictiveBVH/Protocol/Build.lean` |
| `PredictiveBVHResearch/Protocol/Saturate.lean` | broken | `PredictiveBVH/Protocol/Saturate.lean` |
| `PredictiveBVHResearch/Protocol/Fabric.lean` | broken | `PredictiveBVH/Protocol/Fabric.lean` |
| `PredictiveBVHResearch/Interest/AuthorityInterest.lean` | broken | `PredictiveBVH/Interest/AuthorityInterest.lean` |
| `PredictiveBVHResearch/Relativistic/ReBAC.lean` | broken | `PredictiveBVH/Relativistic/ReBAC.lean` |

The Lean `namespace` declarations inside each file are unchanged
(`namespace PredictiveBVH …`), so the names declared inside still live under
the original `PredictiveBVH.*` qualified path. Only the **module path** (which
controls `import …`) was renamed to `PredictiveBVHResearch.*` to avoid
collision with the upstream `optimal-partition` Lake package.

## Build

```sh
lake update    # fetches the upstream `optimal-partition` package
lake build
```

Expected: the build will fail until each module is repaired. Targeted builds
of individual modules (`lake build PredictiveBVHResearch.Spatial.Tree`) are
the unit of repair work.

## Repair roadmap

Tracked in [CONTRIBUTING.md](https://github.com/V-Sekai-fire/multiplayer-fabric-predictive-bvh/blob/main/CONTRIBUTING.md)
(*Deferred items*) on the production-tier repo:

- **Phase 1c** — `sorted_is_ascending_after_build`,
  `aabbQueryB_agrees_with_aabbQueryN` (depends on the
  `insertionSortByHilbert` functionalisation already landed upstream).
- **Phase 2b'** — soundness / completeness for `rayQueryN` / `convexQueryN`.
- **Incremental-branch `tick_agrees_with_build`** — needs a
  window-preservation companion to `resortBucket_preserves_structural`.

Any module repair that lands here should be reflected in the
`Status` column of the table above.
