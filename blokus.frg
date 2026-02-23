#lang forge/froglet

option run_sterling "vis.js"


-- Boolean definition taken from physical keys HW
abstract sig Boolean {}
one sig True, False extends Boolean {}

-- Standard cartesian coordinates
sig Coord {
    x: one Int,
    y: one Int
}

-- A shape is a collection of offsets
// sig Shape {
//     offsets : pfunc Coord -> Boolean
// }

sig Offset {
    pos : one Coord,
    next : lone Offset
}

sig Shape {
    start : one Offset
}

-- A placement represents a shape placed on the board at some anchor coord
// sig Placement {
//     s : one Shape,
//     anchor: one Coord
// }

sig Placement {
    s : one Shape,
    anchor: one Coord
}

-- A board is a grid of placements
one sig Board {
    position : pfunc Coord -> Placement
}

-- We will look at 6x6 boards
pred wellformed {
    -- Coordinate wellformedness
    all c: Coord {
        (c.x < 6) and (c.x >= 0) and (c.y < 6) and (c.y >= 0)
    }

    -- Restrict to 3x3 shapes for now
    // all s: Shape | {
    //     all c: Coord | {
    //         not((c.x < 3) and (c.x >= 0) and (c.y < 3) and (c.y >= 0)) => {
    //             no s.offsets[c]
    //         }
    //     }
    // }

    -- offsets in a shape should not form a cycle
    all s: Shape | {
        -- there should be no offsets in the shape who are reachable from each other
        all off1, off2: Offset | {
            (reachable[off1, s.start, next] and reachable[off2, s.start, next]) implies
            not (reachable[off1, off2, next] and reachable[off2, off1, next]) -- Why is this line "and"
        }
    }

    -- all offsets in a shape must be unique
    all s: Shape {
        all offset1, offset2: Offset | {
            -- IF both of the offsets are part of the shape
            ((offset1 = s.start or reachable[offset1, s.start, next]) and (offset2 = s.start or reachable[offset2, s.start, next])) implies 
            -- THEN we have the implication that IF the two offsets have the same coords, they must be the same
            ((offset1.pos.x = offset2.pos.x and offset1.pos.y = offset2.pos.y) implies
            offset1 = offset2)
        }
    }

    -- restrict to 3x3 shapes
    all s: Shape | {
        all offset : Offset | {
            -- if the offset is reachable from the start, needs to have valid coord
            -- ADDED: also must have valid coords if it's the start
            ((offset = s.start) or reachable[offset, s.start, next]) implies 
            (offset.pos.x >= 0 and offset.pos.x <= 2 and offset.pos.y >= 0 and offset.pos.y <= 2)
        }
    }

    -- No two placements have the same anchor or shape
    all p1, p2: Placement | {
        ((p1.anchor = p2.anchor) or (p1.s = p2.s)) => (p1 = p2)
    }

    -- OFFSETS --

    -- Every shape should have an offset at (0,0).
    // all s: Shape | {
    //     some c: Coord | {
    //         (c.x = 0 and c.y = 0)
    //         s.offsets[c] = True
    //     }
    // }

    -- Every shape should have a start at (0, 0)
    all s: Shape | {
        s.start.pos.x = 0
        s.start.pos.y = 0
    }

    -- If a coord (x,y) is included in an offset of a shape, then some adjacent offset must also be
    -- included, unless the shape is the singleton shape.

    // all s: Shape | {
    //     -- Singleton shape
    //     all c: Coord | {
    //         (s.offsets[c] = True) => (c.x = 0 and c.y = 0)
    //     } or (all c: Coord | {
    //          -- All offsets in shape touch some adjacent offset
    //          -- want every offset to be "reachable" from (0,0)
    //         (s.offsets[c] = True) => {
    //             some c1: Coord | {
    //                 s.offsets[c1] = True and (
    //                     -- Right
    //                     (c1.x = add[c.x, 1] and c1.y = c.y) or
    //                     -- Left
    //                     (c1.x = add[c.x, -1] and c1.y = c.y) or
    //                     -- Bottom
    //                     (c1.x = c.x and c1.y = add[c.y, 1]) or
    //                     -- Top
    //                     (c1.x = c.x and c1.y = add[c.y, -1])
    //                 )
    //             }
    //         }
    //     })
    // }

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

    -- Placements actually appear on the board
    // all p: Placement | {
    //     all off: Coord | {
    //         (p.s.offsets[off] = True) => {
    //             some c2: Coord | {
    //                 c2.x = add[p.anchor.x, off.x]
    //                 c2.y = add[p.anchor.y, off.y]
    //                 Board.position[c2] = p
    //             }
    //         }
    //     }
    // }

    -- placments appear on the board
    all p : Placement | {
        all offset: Offset | {
            -- offset reachable from start or offset = start
            (offset = p.s.start or reachable[offset, p.s.start, next]) implies
            {
                some c: Coord | {
                    c.x = add[p.anchor.x, offset.pos.x]
                    c.y = add[p.anchor.y, offset.pos.y]
                    Board.position[c] = p
                }
            }
        }
    }

    -- NEW: every occupied cell must correspond to some shape's offset
    all c: Coord | {
        some Board.position[c] => {
            some o: Offset | {
                -- There is some offset which is either the start of the occupying shape or reachable
                -- from the start of the occupying shape
                ((o = Board.position[c].s.start) or (reachable[o, Board.position[c].s.start, next]))

                -- and the offset must match
                c.x = add[Board.position[c].anchor.x, o.pos.x]
                c.y = add[Board.position[c].anchor.y, o.pos.y]
            }
        }
    }
    
}

pred onePiece {
    -- Exactly one placement on the board
    all c1, c2: Coord | {
        (some Board.position[c1] and some Board.position[c2]) => {
            Board.position[c1] = Board.position[c2]
        }
    }
    some c1: Coord | {
        some Board.position[c1]
    }
}


pred init {
    -- The board is empty
    all c: Coord | {
        no Board.position[c]
    }
}



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

run {
    wellformed
  //  init
    onePiece

    // Consider size 3 shapes
    all s: Shape | {
        #{offset : Offset | (offset = s.start or reachable[offset, s.start, next]) } = 7
    }

} for exactly 1 Shape, 1 Placement, 5 Int, 7 Coord, 7 Offset
