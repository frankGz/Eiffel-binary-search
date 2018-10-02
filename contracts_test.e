--| CONTRACTS_TEST
--|-----------------------------------------------------------------------------
--|   Copyright (C) GunnarGotshalks --  All rights reserved.
--|
--| Permission to use, copy, modify, and distribute,without fee this software
--| and its documentation for educational purposes and is hereby granted.
--|-----------------------------------------------------------------------------

note
  description: "Contracts start of execution"

class CONTRACTS_TEST

create make

--------------------------------------------------------------------------------
feature {NONE} -- Initialization

make
  local
    algorithm : CONTRACTS
    a : ARRAY[TROLL]
    answer : INTEGER
    a_troll : TROLL
  do
    io.put_string("Start of test%N")
    create algorithm
    create a_troll.make("not a troll", -1)
    create a.make_filled (a_troll, 1, 20)
    array1(a)
    display(a)

    -- Search for an existing troll
    create a_troll.make ("Troll_5", 10)
    answer := algorithm.binary_search (a, a_troll)
    io.put_string ("The found troll is at index " + answer.out + "%N")

    -- Search for an non-existing troll
    create a_troll.make ("Troll_x", 11)
    answer := algorithm.binary_search (a, a_troll)
    io.put_string ("The troll is not found index is Min_int " + answer.out + "%N")

    -- Check example agents
    io.put_string ("%NResult of testing example agents is: " +
                   algorithm.use_example_quantifiers.out + "%N")
    io.put_string ("%NEnd of test%N")
  end

array1 (a : ARRAY[TROLL])
  -- Create version 1 of array.  An item is in the array
  local
    j : INTEGER       -- index to array
    a_troll : TROLL
    name : STRING
  do
    from j := a.lower
    invariant -- forall k : 1 .. j-1 :: created(a[k])
    until j > a.upper
    loop
      create name.make_empty
      name.append ("Troll_" + j.out)
      create a_troll.make (name, j*2)
      a[j] := a_troll
      j := j + 1
    variant a.count - j + 1
    end
  end

display (a : ARRAY[TROLL])
  local	j : INTEGER
  do
    io.new_line
    from j := a.lower
    invariant -- forall k : 1 .. j-1 :: displayed(a[k])
    until j > a.upper
    loop
      io.put_string (j.out + ": " + a[j].name + " is of size " +  a[j].size.out + "%N")
      j := j + 1
    variant a.count - j + 1
    end
    io.new_line
  end
end
