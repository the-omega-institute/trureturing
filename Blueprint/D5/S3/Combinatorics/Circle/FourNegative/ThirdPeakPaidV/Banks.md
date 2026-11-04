# Original labels and exact unbounded domain

## Abstract

Physical low and high V inventories

The positive chains start at original labels 0,d,d+c,d+c+b and have d-1,c-1,b-1,a-1 occurrences. The terminals are d-1,d+c-1,d+c+b-1,k-1, where k=a+b+c+d. A stock is the increasing decoder of set bits in its original chain; complementary stocks partition labels even when source values coincide.

The low V block contains V[0] through V[c-d-1] and has mask m-1. Bit e of h selects exactly original V[c-d+e], for e<d-1; its original-coordinate mask is mh. This high stock and its bitwise complement partition all remaining original V occurrences. Their masses are mh times the V head and m(2^(d-1)-1-h) times that head.

The W mask is 2^(b-a-1). The four banks are U(full)++V(low), V(high complement), W(complement of w)++V(high h), and X(full)++W(w). Inserting each original terminal after its bank gives a permutation of every original label. The source-weight sum identities hold for either row of actual source values. SourceCertificate consumes banks_inventory, banks_good, banks_masses and v_stock_masks. Their live proofs use the stock and high-block partitions, the complete original inventory, stock_mass, complement_mass and high_mass; no separate singleton or high-stock mass theorem is required.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Masks](../MaxPlusTwo/Chambers/Masks.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Endpoint](../PacketNormalForm/Endpoint.md)
