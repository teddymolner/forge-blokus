#lang forge/froglet

-- Boolean definition taken from physical keys HW
abstract sig Boolean {}
one sig True, False extends Boolean {}

-- Standard cartesian coordinates
sig Coord {
    x: one Int,
    y: one Int
}

-- A shape is a collection of offsets
sig Shape {
    offsets : pfunc Coord -> Boolean

}

-- A placement represents a shape placed on the board at some anchor coord
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
    all s: Shape | {
        all c: Coord | {
            not((c.x < 3) and (c.x >= 0) and (c.y < 3) and (c.y >= 0)) => {
                no s.offsets[c]
            }
        }
    }

    -- No two placements have the same anchor or shape
    all p1, p2: Placement | {
        ((p1.anchor = p2.anchor) or (p1.s = p2.s)) => (p1 = p2)
    }

    -- OFFSETS --

    -- Every shape should have an offset at (0,0).
    all s: Shape | {
        some c: Coord | {
            (c.x = 0 and c.y = 0)
            s.offsets[c] = True
        }
    }

    -- If a coord (x,y) is included in an offset of a shape, then some adjacent offset must also be
    -- included, unless the shape is the singleton shape.

    all s: Shape | {
        -- Singleton shape
        all c: Coord | {
            (s.offsets[c] = True) => (c.x = 0 and c.y = 0)
        } or (all c: Coord | {
             -- All offsets in shape touch some adjacent offset
            (s.offsets[c] = True) => {
                some c1: Coord | {
                    s.offsets[c1] = True and (
                        -- Right
                        (c1.x = add[c.x, 1] and c1.y = c.y) or
                        -- Left
                        (c1.x = add[c.x, -1] and c1.y = c.y) or
                        -- Bottom
                        (c1.x = c.x and c1.y = add[c.y, 1]) or
                        -- Top
                        (c1.x = c.x and c1.y = add[c.y, -1])
                    )
                }
            }
        })
    }

    -- No two coordinates should have the same x and y
    all c1, c2: Coord | {
        ((c1.x = c2.x) and (c1.y = c2.y)) => (c1 = c2)
    }

    
}


run {
    wellformed
    some s: Shape | {
        #{c : Coord | s.offsets[c] = True} = 4
    }
} for exactly 1 Shape
