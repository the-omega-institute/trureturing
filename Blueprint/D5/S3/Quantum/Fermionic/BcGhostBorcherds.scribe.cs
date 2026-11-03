using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostBorcherdsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full signed all-integer Borcherds identity on the original occupation ghost carrier.",
        H("Full signed ghost Borcherds identity"), Blocks(
            Paragraph(Text("The carrier is the original complex CountableOccupationFock.Fock: finite linear combinations of finite occupation subsets of the natural numbers. Y is literally BcGhostStateField.Y. Write mu(a,n,b) for the normalized mode (Y(a))[[n]] applied to b; normalized mode n is the Laurent coefficient at -n-1. The integer binomial coefficient is Ring.choose, cast from the integers to the complex numbers, and epsilon(r)=(-1)^r is the integer power.")),
            Paragraph(Text("Let a,b be any original homogeneous states, with parity(a)=(-1)^pa a and parity(b)=(-1)^pb b for natural pa,pb. The third state c is arbitrary. For every integer triple p,q,r, the left coefficient family is choose(p,i) mu(mu(a,r+i,b),p+q-i,c). The first right family is (-1)^i choose(r,i) mu(a,p+r-i,mu(b,q+i,c)); the second is (-1)^i choose(r,i) epsilon(r)(-1)^(pa*pb) mu(b,q+r-i,mu(a,p+i,c)). Each family has finite support in the natural offset i on that actual input.")),
            Describe.Lean(DescribeId.Create("bc-ghost-full-signed-borcherds"),
                DeclarationHandle.Create("D5/S3/Quantum/Fermionic/BcGhostBorcherds.borcherds"),
                H("Three finite supports and all integer indices"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("All three coefficient families have finite support and the sum of the left family equals the sum of the first right family minus the second. The reverse term retains exactly epsilon(r) times (-1)^(pa*pb). Negative p,q,r, zero states, arbitrary third states and every occupation colour remain in scope. There is no supplied Jacobi, residue closure, locality or global finite cutoff premise."))),
                DescribeRole.Theorem),
            Paragraph(Text("Actual Hahn truncation bounds the three unweighted coefficient families separately: the inner products use Y(a)b, Y(b)c and Y(a)c. Multiplication by the integer binomial weights preserves their pointwise finite support. The signed iterate theorem supplies the p=0 seed. Actual signed locality and truncation of Y(a)b supply a high-r zero region. Finite Pascal reindexing gives the discrepancy recurrence D(p+1,q,r)=D(p,q+1,r)+D(p,q,r+1). Induction on nonnegative p and nested induction on negative p and the distance below the high-r boundary give the complete integer domain.")),
            Paragraph(Text("The ordinary finite coefficient and Pascal proof is adapted from LatticeAllStateJacobi; its PolynomialFockJacobi supplier retains Scott Carnahan attribution. The public BinomialKernelDelta.finsum_split, chooseSign_pascal and FieldDeltaBinomial.delta_binomial are reused. The original source is ScottCarnahan/vertexAlg, revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, VertexAlg/VertexBasic/VertexOperator.lean, Apache-2.0. Matsuo-Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1 provide the locality and reconstruction context. The signed coefficient argument is checked on the original occupation carrier.")),
            Paragraph(Text("This is the full three-index algebraic ghost-field law. Coupled matter-ghost signed Jacobi, the original Q field derivation, physical no-ghost and positivity, Monster moonshine, fusion categories, string theory and AdS/CFT remain separate mathematical and physical obligations.")))));
}
