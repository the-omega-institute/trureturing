using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundaryTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cylinder path sums extend from finite increments to the common real edge ell2 on the fixed golden biased boundary.",
        H("The Biased Boundary Trace"), Blocks(
            Def("b", "The right-child mass b is the square of the reciprocal golden ratio a. Their sum is one."),
            Def("Omega", "A ray is a function from the natural numbers to Bool. The value false is the left branch and true is the right branch."),
            Def("bit", "The letter law gives mass a to false and mass b to true."),
            Def("M", "M is the infinite product of this same letter law at every coordinate."),
            Def("G", "G is real L2 for M. Every finite path sum and its limit belong to this fixed space."),
            Def("cylinder", "The cylinder of p prescribes precisely its original initial address coordinates. The empty cylinder is the entire ray space."),
            Describe.Lean(DescribeId.Create("biasedboundarytrace-cylinder-measurable"),
                DeclarationHandle.Create(Prefix + "cylinder_measurable"), H("Measurable Prefix Cylinders"),
                StatementSource.FromAuthor(All("p",Call("Address"),Call("MeasurableSet",Call("cylinder",V("p"))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every finite prefix cylinder is measurable for the original product sigma algebra, including the empty prefix. This allows the original cylinder integrals to determine boundary vectors."))), DescribeRole.Theorem),
            Def("mass", "The cylinder mass is the product of the biased letter probabilities along its finite address."),
            Def("indicator", "A unit increment at a nonempty address is the L2 indicator of its cylinder."),
            Def("J", "J is the continuous linear extension of the actual cylinder indicator sum on finitely supported increments. Its domain is the original real edge ell2 H."),
            Describe.Lean(DescribeId.Create("biasedboundarytrace-a-pos"),
                DeclarationHandle.Create(Prefix + "a_pos"), H("Positive Left Probability"),
                StatementSource.FromAuthor(Seq(D(0),Lt,Sp,V("a"))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The reciprocal golden ratio a is strictly positive because the golden ratio is positive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("biasedboundarytrace-a-lt-one"),
                DeclarationHandle.Create(Prefix + "a_lt_one"), H("Strict Contraction of Mass"),
                StatementSource.FromAuthor(Seq(V("a"),Lt,Sp,D(1))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The left probability a is strictly smaller than one because the golden ratio exceeds one. Hence powers of a decay to zero, giving a common finite depth for every positive mass threshold."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("biasedboundarytrace-sum-weights"),
                DeclarationHandle.Create(Prefix + "sum_weights"), H("Conservation of Probability"),
                StatementSource.FromAuthor(Seq(V("a"),Plus,V("b"),Eq,D(1))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The golden conjugate equation gives a plus its square equal to one. Thus the two child probabilities a and b sum to one at every vertex."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("biasedboundarytrace-cylinder-mass"),
                DeclarationHandle.Create(Prefix + "cylinder_mass"), H("Actual Cylinder Mass"),
                StatementSource.FromAuthor(All("p",Call("Address"),
                    Seq(Call("toReal",Call("M",Call("cylinder",V("p")))),Eq,Call("mass",V("p"))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original finite address p, including the empty address, the real mass of its cylinder under the infinite Bernoulli product M is exactly the product of its letter probabilities: a for false and b for true.")),
                    Paragraph(Text("The finite-coordinate product formula for M reduces the cylinder measure to singleton probabilities. Appending one letter multiplies both that measure and mass(p) by the same probability. The empty address has mass one. Consequently this is the actual cylinder mass used by the mass-crossing frontier."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("biasedboundarytrace-single"),
                DeclarationHandle.Create(Prefix + "J_single"), H("An Actual Single Increment"),
                StatementSource.FromAuthor(All("p",Call("Edge"),All("c",Seq(Mathbb,Grp(V("R"))),
                    Seq(Call("J",Call("single",D(2),V("p"),V("c"))),Eq,Mul(V("c"),Call("indicator",V("p"))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original nonempty edge p and real increment c, J sends the square-summable single-coordinate vector to c times the actual biased cylinder indicator. This identifies the coordinate covariance with the intersection probabilities of the same measure M."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("biasedboundarytrace-hardy"),
                DeclarationHandle.Create(Prefix + "boundary_trace_hardy"), H("Convergence and Hardy Tail"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every square-summable real increment vector, the sum of its weighted cylinder indicators converges in L2 to Jz. The sum is over all nonempty original addresses, and convergence is along finite subsets.")),
                    Paragraph(Text("For every natural depth h, including zero, removing the coordinates of length at most h leaves a trace with squared norm at most a to the power h+1 divided by 1-a times the original squared edge norm.")),
                    Paragraph(Text("A ray has at most one prefix of each length. Weighted Cauchy-Schwarz and the geometric sum bound its finite path sum. Integrating each cylinder term introduces its actual biased mass, bounded above by a to the address length. This cancels the reciprocal weight and leaves the real ell2 energy.")),
                    Paragraph(Text("The finite-increment inclusion has dense range in H. The uniform finite-sum estimate extends the path map continuously, and the canonical single-coordinate expansion in ell2 gives its L2 sum formula. Passing the finite Hardy estimate to this limit proves the all-vector tail.")),
                    Paragraph(Text("The conditional suffix identity, the stopping-cylinder projection and its residual estimate require additional results. No spectral counting, compact resolvent or free-root form identification follows from this statement alone."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string prose) => Describe.Lean(
        DescribeId.Create("biasedboundarytrace-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula All(string s, Formula t, Formula x) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(x));
    private static Formula Mul(Formula x, Formula y) => Seq(Par(x), Sp, Cdot, Sp, Par(y));
    private static Formula Sub(Formula x, Formula y) => Seq(Par(x), Sp, Minus, Sp, Par(y));
    private static Formula Pow(Formula x, Formula y) => Seq(Par(x), Caret, Grp(y));
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Sp, Vert);
    private static Formula ResultFormula()
    {
        Formula h=V("h"), z=V("z"), p=V("p");
        Formula sum=Call("HasSum", Par(Seq(p, Colon, Sp, Call("Edge"), Sp, Mapsto, Sp, Mul(Call("coordinate",z,p),Call("indicator",p)))), Call("J",z));
        Formula coeff=Seq(Frac, Grp(Pow(V("a"),Seq(h,Plus,D(1)))), Grp(Sub(D(1),V("a"))));
        Formula bound=Seq(Pow(Norm(Call("J",Sub(z,Call("P",h,z)))),D(2)),Leq,Mul(coeff,Pow(Norm(z),D(2))));
        return Seq(Par(All("z",Call("H"),sum)),Land,
            Par(All("h",Seq(Mathbb,Grp(V("N"))),All("z",Call("H"),bound))));
    }
}
