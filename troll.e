note
	description: "Objects that represent trolls."
	author: "Gunnar Gotshalks"

class TROLL
  inherit COMPARABLE

create make

--------------------------------------------------------------------------------
feature {CONTRACTS_TEST, TROLL} -- Representation

name: STRING
size: INTEGER

--------------------------------------------------------------------------------
feature {NONE} -- Initialization

make (n : STRING; s : INTEGER) -- Initialization for 'Current'.
  require true
  do
    name := n ; size := s
  ensure data_set: name.is_equal(n) and size = s
  end

--------------------------------------------------------------------------------
feature -- Comparison

is_less alias "<" (other: TROLL) : BOOLEAN
    -- Result is true iff the other troll is greater than Current
  do
    if size > other.size then Result := false
    elseif size < other.size then Result := true
    else Result := str_less_than(name, other.name)
    end
  ensure then
    result_ok: Result = (size < other.size)
               or (size = other.size implies str_less_than(name, other.name))
  end

str_less_than (s1, s2 : STRING) : BOOLEAN
    -- Result is true iff s1 < s2
  local j : INTEGER
  do
  	from j := 1 ; Result := true
  	invariant -- forall k : 1 .. j-1 :: s1[k] = s2[k]
  	until Result = false or j > s1.count or j > s2.count
  	loop
  	  Result := s1[j] = s2[j]
  	  j := j + 1
  	variant s1.count.min(s2.count) - j + 1
  	end
    if Result then Result := s1.count < s2.count end
  end

end
