using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using Fml = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class PowerMapSeparationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/PowerMapSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two groups of order 4374 have separately conjugate integer-power maps but no common square-cube conjugacy.",
        H("Separate power maps and a joint obstruction"),
        Blocks(
            Definition("F", "The field of three elements",
                "F is ZMod 3. All seven non-Boolean coordinates and every bilinear expression below are evaluated in this field."),
            Definition("S", "The two original-coordinate carriers",
                "For a Boolean i, S(i) has coordinates (a,b,x,y,z,s,t,e), with the first seven in F and e Boolean. Write v=(a,b), w=(x,y,z) and c=(s,t). False selects the first group G and true the second group H. These are the original, uncentered coordinates, including the free third coordinate z of w in H."),
            Definition("productEquiv", "The finite Cartesian parametrization",
                "For each Boolean i, productEquiv(i) maps (a,b,x,y,z,s,t,e) to ((a,b),(x,y,z),(s,t),e), an equivalence with F squared times F cubed times F squared times Bool. Its inverse unpacks the coordinates. The induced finite structure has cardinality 3 squared times 3 cubed times 3 squared times 2, namely 4374."),
            Definition("sign", "The involution sign",
                "For a Boolean e, sign(e) is minus one if e is true and one otherwise."),
            Definition("B₁", "The first bilinear coordinate",
                "For i,a,b,x,y, B₁(i,a,b,x,y) is ax+by when i is false and ax−by when i is true. The subscript here labels a coordinate of the bilinear map, not the choice of group."),
            Definition("B₂", "The second bilinear coordinate",
                "For i,a,b,x,y,z, B₂(i,a,b,x,y,z) is ay+bz when i is false and bx+ay when i is true. Together B₁ and B₂ define the vector B(i,v,w)."),
            Definition("mulS", "The semidirect-product multiplication",
                "For p=(v,w,c,e) and q=(v′,w′,c′,e′) in S(i), put σ=sign(e). Their product is (v+v′,w+σw′,c+σc′+σB(i,v,w′),e xor e′). Thus the normal subgroup with e=false has bilinear multiplication (v,w,c)(v′,w′,c′)=(v+v′,w+w′,c+c′+B(i,v,w′)), and the nontrivial Boolean element acts by (v,w,c)↦(v,−w,−c)."),
            Definition("oneS", "The identity",
                "For each Boolean i, oneS(i) is (0,0,0,0,0,0,0,false). It is the identity for mulS."),
            Definition("invS", "The inverse",
                "For p=(v,w,c,e) and σ=sign(e), invS(p) is (−v,−σw,−σc+σB(i,v,w),e). Bilinearity proves associativity, and these identity and inverse formulas give the actual Group structure on S(i)."),
            Describe.Lean(DescribeId.Create("power-map-separation-claim"),
                DeclarationHandle.Create(Owner + "claim"), H("The fixed-pair implication"),
                StatementSource.FromAuthor(Disp(Equal(Fml.Id("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In this formula G=S(false), H=S(true), Equiv(G,H) is the type of bijections between the underlying carriers, card is finite cardinality, and Z is the integers. Powers use the group operations just defined. The premise requires a possibly different bijection for each integer m, including zero and negative exponents. The conclusion requires one bijection preserving both natural powers two and three. This implication is posed for this fixed pair, not asserted as a conjecture of an external author."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("power-map-separation-result"),
                DeclarationHandle.Create(Owner + "result"), H("Separate conjugacy does not imply joint conjugacy"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Open, ClaimBody(), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The proof establishes the entire premise and disproves the conclusion. Both actual groups have order 4374. Every integer-power map on G is conjugate to the corresponding map on H, but no bijection preserves both squares and cubes. In particular no single bijection preserves all integer powers.")),
                    Paragraph(Text(
                        "Replace the central coordinate c by c+B(i,v,w). This is an invertible change of coordinates, not a group isomorphism between G and H. Direct calculations relate the actual squares, cubes and inverses to their expressions in these centered coordinates. The identity between centered carriers yields one bijection preserving the identity, cubes and inverses. A second bijection changes w on the e=true part by an invertible map depending on v, chosen so that B(true,v,w′)=B(false,v,w). The case v=0 is included. This bijection preserves squares and therefore fourth powers. Every element has sixth power one, so reduction modulo six supplies conjugacies for every integer exponent, including negative integers.")),
                    Paragraph(Text(
                        "For a nonidentity involution u, define N(u)={x squared : x cubed=u}. A bijection preserving squares and cubes must preserve nonidentity involutions, these neighborhoods, and equality of neighborhoods. In G, the class of nonidentity involutions with a given neighborhood has nine elements; in H it has twenty-seven. The class descriptions follow from the actual coordinates and explicit bijections with F squared and F cubed. Transporting a class through a common square-cube bijection would equate these cardinalities, which is impossible.")),
                    Paragraph(Text(
                        "The argument uses the classical bilinear central extension and its sign action, but constructs the power conjugacies directly. It does not assert the detailed enumeration of every functional-graph component or the classification of all finite groups with this separation."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("power-map-separation-definition-" +
                name.Replace("₁", "one").Replace("₂", "two").ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Bind(FormulaQuantifier q, string name, Formula domain, Formula body) =>
        new Formula.Bind(q, FormulaIdentifier.Create(name), domain, body);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Preserves(Formula m) =>
        Equal(Call("f", Power(Fml.Id("p"), m)), Power(Call("f", Fml.Id("p")), m));
    private static Formula ClaimBody()
    {
        var g = Fml.Id("G");
        var h = Fml.Id("H");
        var bijections = Call("Equiv", g, h);
        var separate = Bind(FormulaQuantifier.ForAll, "m", Seq(Mathbb, Grp(Fml.Id("Z"))),
            Bind(FormulaQuantifier.Exists, "f", bijections,
                Bind(FormulaQuantifier.ForAll, "p", g, Preserves(Fml.Id("m")))));
        var premise = And(Equal(Call("card", g), D(4, 3, 7, 4)),
            And(Equal(Call("card", h), D(4, 3, 7, 4)), separate));
        var joint = Bind(FormulaQuantifier.Exists, "f", bijections,
            Bind(FormulaQuantifier.ForAll, "p", g, And(Preserves(D(2)), Preserves(D(3)))));
        return new Formula.Logic(Seq(Open, premise, Close), FormulaLogicOperator.Implies,
            Seq(Open, joint, Close));
    }
}
