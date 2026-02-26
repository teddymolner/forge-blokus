#lang forge/froglet

option run_sterling "vis_state.js"


-- States represent each turn in the game
sig State {
    position : pfunc Coord -> Placement
}
-- Boolean definition taken from physical keys HW
abstract sig Boolean {}
one sig True, False extends Boolean {}

-- Standard cartesian coordinates
sig Coord {
    x: one Int,
    y: one Int
}

sig Offset {
    pos : one Coord,
    next : lone Offset
}

sig Shape {
    start : one Offset
}

sig Placement {
    s : one Shape,
    anchor: one Coord
}

pred inShape[o: Offset, s: Shape] {
    -- Determine if the given offset is in the shape
    o = s.start or reachable[o, s.start, next]
}

pred coveredByPlacement[c: Coord, p: Placement] {
    -- Determine if placing shape s with anchor a covers coord c on the board.
    some o: Offset | {
        inShape[o, p.s]
        c.x = add[p.anchor.x, o.pos.x]
        c.y = add[p.anchor.y, o.pos.y]
    }
}

pred validCoord[c: Coord] {
    (c.x < 4) and (c.x >= 0) and (c.y < 4) and (c.y >= 0)
}
-- We will look at 6x6 boards
pred wellformed {
    -- Coordinate wellformedness
    all c: Coord {
        validCoord[c]
    }

    -- Optimization: each offset has at most one predecessor
    all o: Offset | {
       lone p: Offset | {
            p.next = o
       }
    }

    -- Restrict to 3x3 shapes for now
    // all s: Shape | {
    //     all c: Coord | {
    //         not((c.x < 3) and (c.x >= 0) and (c.y < 3) and (c.y >= 0)) => {
    //             no s.offsets[c]
    //         }
    //     }
    // }

    -- Offsets in a shape should not form a cycle
    all s: Shape | {
        -- there should be no offsets in the shape who are reachable from each other
        all off1, off2: Offset | {
            (reachable[off1, s.start, next] and reachable[off2, s.start, next]) implies
            not (reachable[off1, off2, next] and reachable[off2, off1, next]) -- Why is this line "and"
        }
    }

    -- All offsets in a shape must be unique
    all s: Shape {
        all offset1, offset2: Offset | {
            -- IF both of the offsets are part of the shape
            ((offset1 = s.start or reachable[offset1, s.start, next]) and (offset2 = s.start or reachable[offset2, s.start, next])) implies 
            -- THEN we have the implication that IF the two offsets have the same coords, they must be the same
            ((offset1.pos.x = offset2.pos.x and offset1.pos.y = offset2.pos.y) implies
            offset1 = offset2)
        }
    }

    -- Restrict to 3x3 shapes
    all s: Shape | {
        all offset : Offset | {
            -- if the offset is reachable from the start, needs to have valid coord
            -- ADDED: also must have valid coords if it's the start
            ((offset = s.start) or reachable[offset, s.start, next]) implies 
            (offset.pos.x >= 0 and offset.pos.x <= 2 and offset.pos.y >= 0 and offset.pos.y <= 2)
        }
    }

    -- No two placements have the same anchor or shape
    --all p1, p2: Placement | {
    --    ((p1.anchor = p2.anchor) or (p1.s = p2.s)) => (p1 = p2)
    --}

    -- Every shape should have a start at (0, 0)
    all s: Shape | {
        s.start.pos.x = 0
        s.start.pos.y = 0
    }

    -- Unless the shape is a singleton shape, the "next" field should only distinguish by 1 coord in a direction
    all s: Shape | {
        -- singleton shape
        no s.start.next or (
            all off1, off2: Offset | {
                // the offsets should be directly above, below, to the left, or to the right
                (off1.next = off2) implies
                (
                    -- Right
                    (off2.pos.x = add[off1.pos.x, 1] and off1.pos.y = off2.pos.y) or
                    -- Left
                    (off2.pos.x = subtract[off1.pos.x, 1] and off1.pos.y = off2.pos.y) or
                    -- Bottom
                    (off1.pos.x = off2.pos.x and off2.pos.y = add[off1.pos.y, 1]) or
                    -- Top
                    (off1.pos.x = off2.pos.x and off2.pos.y = subtract[off1.pos.y, 1])
                )
            }
        )
    }

    -- No two coordinates should have the same x and y
    all c1, c2: Coord | {
        ((c1.x = c2.x) and (c1.y = c2.y)) => (c1 = c2)
    }
}

pred stateWellformed[s: State] {
    -- Placements appear on board
    all c: Coord | validCoord[c] => {
        some s.position[c] => coveredByPlacement[c, s.position[c]]
    }

    --all p: Placement | {
    --    all c: Coord | {
    --        coveredByPlacement[c, p] => s.position[c] = p
    --    }
    --}
}



pred init[s: State] {
    all c: Coord | validCoord[c] => {
        no s.position[c]
    }
}

pred step[s0, s1: State] {
    some p1: Placement | {
        -- p1 will be the new placement for this transition

        -- GUARD:
        all c: Coord | validCoord[c] => {
            -- this placement did not already exist

            -- the coords covered by the new placement were not previously occupied
            coveredByPlacement[c, p1] => (no s0.position[c])
        }

        -- ACTION:

        -- all coordinates covered by placement are now updated, and no others are
        all c: Coord | validCoord[c] => {
            -- newly covered cells become p1
            coveredByPlacement[c, p1] => s1.position[c] = p1

            -- non-covered cells are not changed
            not coveredByPlacement[c, p1] => (s1.position[c] = s0.position[c])
        }
    }
}


------ TESTS ------

test suite for init {
    test expect {
        initMeansEmpty : {
            wellformed => {all s: State | {
                init[s] => (all c: Coord | {
                    no s.position[c]
                })}
            }
        } is checked
    }
}

test suite for stateWellformed {
     test expect {
        stateWellformedRespectsCoverage : {
            wellformed => {
                all s: State | stateWellformed[s] => {
                    all c: Coord | validCoord[c] => {
                        some s.position[c] => {
                            coveredByPlacement[c, s.position[c]]
                        }
                    }
                }
            }
        } is checked
    }
}

test suite for step {
    test expect {
        stepNeverChangesPreviousPositions : {
            all s0, s1: State | {
                step[s0,s1] => {
                    all c: Coord | validCoord[c] => {
                        (some s0.position[c]) => (s1.position[c] = s0.position[c])
                    }
                }
            }
        } is checked
        positionChangingIsUnsat : {
            some s0, s1: State, c: Coord | {
                validCoord[c]
                stateWellformed[s0] and stateWellformed[s1]
                step[s0, s1]
                some s0.position[c]
                some s1.position[c]
                s1.position[c] != s0.position[c]
            }
        } is unsat
    }

    
}



------- RUNS -------

--#run {
 --   wellformed
--    some s: Shape | {
--        #{c : Coord | s.offsets[c] = True} = 4
--    }
--} for exactly 1 Shape

--run {
--    wellformed
--
--    #{c : Coord | some Board.position[c]} = 7
--
--    some s: Shape | {
--        #{offset : Offset | (offset = s.start or reachable[offset, s.start, next]) } = 7
--    }
--
--} for exactly 1 Shape, 1 Placement, 5 Int, 7 Coord, 7 Offset

// run {
//     wellformed
//     some s0, s1, s2: State | {
//         init[s0]
//         stateWellformed[s0]
//         stateWellformed[s1]
//         stateWellformed[s2]
//         step[s0,s1] and step[s1, s2]

//         -- State 1 places piece at origin
//         all c: Coord | validCoord[c] => {
//             ((c.x = 0) and (c.y = 0)) => {
//                 some s1.position[c]
//             }

//             -- State 1 also has a piece touching at (1,1)
//             ((c.x = 1) and (c.y = 1)) => {
//                 some s1.position[c]
//             }
//         }

//        -- there is exactly one placement used in s1, and it covers exactly 3 cells
//         one p: Placement | {
//             all c: Coord | validCoord[c] => (some s1.position[c] <=> s1.position[c] = p)
            
//             #{c: Coord | validCoord[c] and s1.position[c] = p} = 3

//             -- p forms an L (not all in one row or one column)
//             let cells = {c: Coord | validCoord[c] and s1.position[c] = p} | {
//                 not (
//                     -- all same x  (vertical line)
//                     (all c1, c2: cells | c1.x = c2.x)
//                     or
//                     -- all same y (horizontal line)
//                     (all c1, c2: cells | c1.y = c2.y)
//                 )
//             }
//         }

//         -- All shapes in S2 have size 3
//         all c: Coord | validCoord[c] => {
//             some s2.position[c] => ((#{c1: Coord | s2.position[c1] = s2.position[c]}) = 3)
//         }


//     }

//     --some s: Shape | {
//     --    #{offset : Offset | (offset = s.start or reachable[offset, s.start, next]) } = 3
//     --}
// } for exactly 5 Int, 16 Coord, 7 Offset, 2 Placement, 2 Shape, 3 State




run {
    wellformed
    some s0, s1, s2, s3, s4: State | {
        init[s0]
        stateWellformed[s0]
        stateWellformed[s1]
        stateWellformed[s2]
        stateWellformed[s3]
        stateWellformed[s4]
        step[s0,s1] and step[s1, s2]
        step[s2,s3] and step[s3, s4]

        -- State 1 places piece at origin
        all c: Coord | validCoord[c] => {
            ((c.x = 0) and (c.y = 0)) => {
                some s1.position[c]
            }
        }
    }
    --some s: Shape | {
    --    #{offset : Offset | (offset = s.start or reachable[offset, s.start, next]) } = 3
    --}
} for exactly 5 Int, 16 Coord, 10 Offset, 4 Placement, 4 Shape, 5 State

