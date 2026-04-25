-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee

import Lake
open System Lake DSL

package «predictive-bvh-research» where

-- Production-tier package: provides Primitives.Types, Formulas.*,
-- Spatial.HilbertBroadphase, Relativistic.NoGod, etc. The research-tier
-- proofs in this repo import those modules unchanged.
require «optimal-partition» from git
  "https://github.com/V-Sekai-fire/multiplayer-fabric-predictive-bvh.git" @ "main"

@[default_target]
lean_lib «PredictiveBVHResearch» where
  roots := #[`PredictiveBVHResearch]
