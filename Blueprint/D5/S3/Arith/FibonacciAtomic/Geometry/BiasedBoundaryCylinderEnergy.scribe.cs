using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundaryCylinderEnergyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderEnergy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant traces have unit fixed-root minimum on the original biased boundary, and the depth-two and depth-one cylinder indicators have mixed free-root energy one eighth.",
        H("Cylinder Energies on the Original Boundary"), Blocks(
            Def("rootEdge", "For a Boolean letter c, rootEdge(c) is the original nonempty one-letter address [c]. False denotes L and true denotes R."),
            Describe.Lean(DescribeId.Create("constant-trace-minimum"),
                DeclarationHandle.Create(Prefix + "constant_trace_minimum"), H("The Constant-Trace Minimum"),
                StatementSource.FromAuthor(Minimum()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("H is the original real square-summable space on nonempty ordered Boolean addresses. J maps H to real L2 of the golden biased product measure M. Constants, conditional suffixes and all equalities of traces use this same M. In the displayed formula, eval(q,p) is the original increment coordinate q(p), and inner is the real inner product on H.")),
                    Paragraph(Text("Project the sum of the two unit root increments onto the orthogonal complement of the kernel of J. The result has constant trace one and is the fixed-root minimum. Pairing it with any constant trace c gives c times its squared norm.")),
                    Paragraph(Text("The adjoints of the two original suffix restrictions insert disjoint strict-descendant increments. Their pairing formula gives an exact decomposition of squared edge norm into the two root squares and the two suffix squared norms. Conditional pullback gives the corresponding decomposition of the actual trace.")),
                    Paragraph(Text("Write m for the squared norm of the minimum. Inserting half of it below each root edge, with root increments one half, gives another constant-one trace of squared norm (1+m)/2. Minimality gives m at most one. Applying minimality to the two suffixes of the minimum and completing their two squares gives m at least one. The squared norm is therefore one. Equality identifies the inserted vector with the minimum and gives both equal-split identities.")),
                    Paragraph(Text("Consequently every original increment vector with constant trace c has squared norm at least c squared. The pairing identity applies to all such vectors, not just finite increments or traces defined pointwise on every ray."))), DescribeRole.Theorem),
            Def("cylinderD", "For any original nonempty edge p, cylinderD(p) is its actual cylinder indicator in the original free-root domain D. Root coefficient zero and the unit single-edge increment give its domain membership."),
            Describe.Lean(DescribeId.Create("mixed-cylinder-energy"),
                DeclarationHandle.Create(Prefix + "mixed_cylinder_energy"), H("The Mixed Cylinder Energy"),
                StatementSource.FromAuthor(Seq(Call("form",Call("cylinderD",Call("descendant",ListOf(V("false")),Call("rootEdge",V("false")))),
                    Call("cylinderD",Call("rootEdge",V("false")))),Eq,Seq(Frac,Grp(D(1)),Grp(D(8))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A is the actual indicator of [L] and B is the actual indicator of [LL]. The form pairs their unique effective least-increment lifts in the original free-root domain, with the root coefficient optimized freely.")),
                    Paragraph(Text("For A, the root coefficient is one half, its two root increments are one quarter and minus one quarter, and its strict suffixes are these same multiples of the constant-one minimum. For B, the root coefficient is one quarter and the two root increments are one eighth and minus one eighth. At the next level the increments are five sixteenths, minus three sixteenths, minus one sixteenth and minus one sixteenth; each corresponding strict suffix is that increment times the constant-one minimum.")),
                    Paragraph(Text("The conditional pullbacks identify these traces with the original two indicators. Pairing either increment vector with an arbitrary vector in the kernel of the centered trace cancels at every junction and at the free root. Both vectors therefore lie in the original effective space K. The existing attained free-root variational theorem identifies them with the actual lifts.")),
                    Paragraph(Text("The root edges contribute one sixteenth to their inner product. The left suffix contributes one thirty-second and the right suffix contributes one thirty-second, giving one eighth. This identity is an energy statement on the original form; a real-time non-Markov law requires its further process-law argument."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string prose) => Describe.Lean(
        DescribeId.Create("cylinder-energy-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string x) => F.Id(x);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula Call(string x, params Formula[] xs) => new Formula.Apply(Seq(Operatorname,Grp(V(x))),[..xs]);
    private static Formula All(string x, Formula t, Formula b) => Seq(Forall,Sp,V(x),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula ListOf(Formula x) => Seq(OpenBracket,x,CloseBracket);
    private static Formula Sq(Formula x) => Seq(Par(x),Caret,Grp(D(2)));
    private static Formula NormSq(Formula x) => Sq(Seq(Vert,Sp,x,Sp,Vert));
    private static Formula And(params Formula[] xs) => Seq([..xs.SelectMany((x,i) => i == 0 ? new[]{Par(x)} : new[]{Land,Sp,Par(x)})]);
    private static Formula Minimum()
    {
        Formula q=V("q"), c=V("c"), z=V("z");
        Formula pair=All("c",Seq(Mathbb,Grp(V("R"))),All("z",V("H"),
            Seq(Call("J",z),Eq,Call("constG",c),Implies,Sp,Call("inner",q,z),Eq,c)));
        Formula split=All("c",V("Bool"),And(
            Seq(Call("eval",q,Call("rootEdge",c)),Eq,Seq(Frac,Grp(D(1)),Grp(D(2)))),
            Seq(Call("S",ListOf(c),q),Eq,Seq(Frac,Grp(D(1)),Grp(D(2))),Cdot,Sp,q)));
        return Seq(Exists,Sp,q,Colon,Sp,V("H"),Comma,Sp,Par(And(
            Seq(Call("J",q),Eq,Call("constG",D(1))),Seq(NormSq(q),Eq,D(1)),pair,split)));
    }
}
