--| CONTRACTS
--|-----------------------------------------------------------------------------
--|   Copyright (C) GunnarGotshalks --  All rights reserved.
--|
--| Permission to use, copy, modify, and distribute,without fee this software
--| and its documentation for educational purposes and is hereby granted.
--|-----------------------------------------------------------------------------

note
  description: "Executable contract exercise"
  author: "??? Your name ???"
  date: "??? Date ???"

class CONTRACTS

--------------------------------------------------------------------------------
feature -- Algorithms

binary_search (trolls : ARRAY[TROLL]; key : TROLL) : INTEGER
  require

    -- ???
  local low, mid, high : INTEGER
  do
    from  low := trolls.lower ; high := trolls.upper ;  Result := Result.min_value --lower: min index, upper: max index, min value: extreme small number
    invariant -- ???
    until Result /= Result.min_value or low > high
    loop
      mid := (low + high)//2
      if trolls[mid].is_equal(key) then Result := mid
      elseif trolls[mid].is_less(key) then low := mid + 1
      else high := mid - 1
      -- variant ???
      end
    end
  ensure
    -- ???
  end

--------------------------------------------------------------------------------
feature -- Your Quantifiers

for_all_in_array(the_array : ARRAY[TROLL];
							length : INTEGER
							predicate : FUNCTION[TUPLE[TROLL, INTEGER],BOOLEAN]):BOOLEAN
	local array_copy : ARRAY[TROLL]
	do
		Result := true
		array_copy := the_array.twin
		from array_copy.lower
		until array_copy.upper
		loop
			Result := predicate.item(array_copy.item , length)
			array_copy.
		end
	end

--------------------------------------------------------------------------------
feature -- Your Agents

--------------------------------------------------------------------------------
feature -- Example Quantifiers

for_all_in(the_list : LINKED_LIST[STRING];
           length: INTEGER
           predicate : FUNCTION[TUPLE[STRING, INTEGER], BOOLEAN]) : BOOLEAN
  -- Result is True if the predicate is true for all items in the_list.
  local list_copy : LINKED_LIST[STRING]
  do
    Result := True
    list_copy := the_list.twin
    from list_copy.start
  	invariant
  	  -- forall item : the_list | 1 <= index_of(item) <= index(list_copy)-1
      --        :: predicate(item)}
    until list_copy.after or not Result
    loop
      Result := predicate.item(list_copy.item, length)
      list_copy.forth -- move the indeicator to next
    variant  list_copy.count + 1 - list_copy.index
    end
  end

there_exists_in(the_list : LINKED_LIST[STRING];
                predicate : FUNCTION[TUPLE[STRING],BOOLEAN]) : BOOLEAN
  -- Is the 'predicate' true for at least one of the items in the list?
  local list_copy : LINKED_LIST[STRING]
  do
    list_copy := the_list.twin
  	from list_copy.start
  	invariant
  	  -- forall item : the_list | 1 <= index_of(item) <= index(list_copy)-1
          --        :: not predicate(item)}
  	until list_copy.after or Result
  	loop
  	  Result := predicate.item([list_copy.item])
  	  list_copy.forth
    variant  list_copy.count + 1 - list_copy.index
  	end
  end

there_exists1_in(the_list : LINKED_LIST[STRING];
                 predicate : FUNCTION[TUPLE[STRING],BOOLEAN]) : BOOLEAN
  -- Is the 'predicate' true for exactly one of the items in the list?
  local list_copy : LINKED_LIST[STRING]
        count_exists : INTEGER
  do
    list_copy := the_list.twin
  	from list_copy.start
  	invariant
  	  -- count_exists = #{ item : the_list
      --                 | 1 <= position_of(item) <= index(list_copy)-1
      --                   and prediate(item)}
  	until list_copy.after
  	loop
  	  if predicate.item([list_copy.item])
        then count_exists := count_exists + 1 end
  	  list_copy.forth
    variant  list_copy.count + 1 - list_copy.index
  	end
  	Result := count_exists = 1
  end

--------------------------------------------------------------------------------
feature -- Example Agents

length_of_string_is(a_string: STRING; length: INTEGER) : BOOLEAN
  do
    Result := a_string.count = length
  end

--------------------------------------------------------------------------------
feature -- Using example quantifiers

use_example_quantifiers : BOOLEAN
  -- Result is True for all tested quantifiers
  local
    list_1: LINKED_LIST[STRING]
    list_2: LINKED_LIST[STRING]
    list_3: LINKED_LIST[STRING]
  do
    create list_1.make ; create list_2.make ; create list_3.make
    load_the_lists(list_1, list_2, list_3)
    Result := for_all_in(list_1, 3, agent length_of_string_is(?,?))
    Result := Result and there_exists_in(list_2, agent length_of_string_is(?,3))
    Result := Result and there_exists1_in(list_3, agent length_of_string_is(?,3))
  end

load_the_lists(list_1, list_2, list_3: LINKED_LIST[STRING])
  do
      -- list_1 has all items of length 3.
    list_1.extend ("123") ; list_1.extend ("456") ;list_1.extend ("789") ;

      -- list_2 has 2 items of length 3.
    list_2.extend ("12") ; list_2.extend ("456") ;list_2.extend ("789") ;

      -- list_3 has 1 item of length 3.
    list_3.extend ("12") ; list_3.extend ("456") ;list_3.extend ("89") ;

  end

end
