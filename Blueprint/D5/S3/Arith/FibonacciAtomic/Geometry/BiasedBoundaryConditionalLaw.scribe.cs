using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundaryConditionalLawDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prepending a finite address pushes the actual golden biased Bernoulli law to its normalized restriction, giving a bounded conditional composition on the common boundary L2.",
        H("The Actual Conditional Suffix Law"), Blocks(
            Def("tail", "Deleting n initial coordinates shifts a ray to its suffix. Under the original infinite product law this suffix again has law M."),
            Def("prepend", "Prepending p prescribes its original finite coordinates and shifts an arbitrary suffix ray to start after them."),
            Def("conditional", "The conditional measure is the restriction of the original M to the actual cylinder of p, divided by that cylinder's mass. The mass is positive and finite for every p, including the empty prefix."),
            Def("pullbackBound", "The conditional composition bound is the real value of the reciprocal cylinder mass raised to one half."),
            Def("pullback", "The conditional pullback is a continuous linear map from the original G to itself. It composes a representative with prepend, using the normalized restricted target measure to establish square integrability and independence of representatives."),
            Def("conditionalTrace", "The conditional trace composes this bounded pullback with the original all-ell2 trace J, retaining L2(M) as its suffix codomain."),
            Describe.Lean(DescribeId.Create("biasedboundaryconditionallaw-pullbacklaw"),
                DeclarationHandle.Create(Prefix + "conditional_pullback_law"), H("Disintegration and Bounded Pullback"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every finite prefix, pushing the restricted measure forward by deletion gives the original law multiplied by the cylinder mass. Equivalently, prepending pushes M to its actual normalized restricted measure. This includes the empty prefix, whose conditional measure is M.")),
                    Paragraph(Text("The prescribed finite coordinates and the remaining coordinates are independent under the same infinite product measure. The suffix reindexing has law M. On the prescribed cylinder, prepend after deletion is the identity, which transports the restricted suffix law back to the normalized cylinder law.")),
                    Paragraph(Text("For every F in the original G, the pullback equals composition with prepend almost everywhere for M, and its norm is bounded by the reciprocal square root of the cylinder mass times the norm of F. Consequently this representative identity also holds for the joined J applied to every vector of the original H. Deleting a prepended prefix recovers every suffix ray exactly.")),
                    Paragraph(Text("The exceptional representative set may depend on the vector. The prefix-constant plus J of strict suffix increments, the mass-stopping conditional projection, the centered residual identity and its weighted norm decomposition require additional proofs. No spectral operator or counting result is asserted."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string prose) => Describe.Lean(
        DescribeId.Create("biasedboundaryconditionallaw-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula All(string s, Formula t, Formula x) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(x));
    private static Formula Mul(Formula x, Formula y) => Seq(Par(x), Sp, Cdot, Sp, Par(y));
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Sp, Vert);
    private static Formula ResultFormula()
    {
        Formula p=V("p"), f=V("F"), z=V("z"), w=V("w"), addr=Call("Address"), omega=Call("Omega");
        Formula cyl=Call("cylinder",p), mass=Call("M",cyl), cond=Call("conditional",p), pre=Call("prepend",p), shift=Call("tail",Call("length",p));
        Formula positive=All("p",addr,Seq(mass,Neq,D(0)));
        Formula deletion=All("p",addr,Seq(Call("map",Call("restrict",V("M"),cyl),shift),Eq,Mul(mass,V("M"))));
        Formula law=All("p",addr,Call("MeasurePreserving",pre,V("M"),cond));
        Formula empty=Seq(Call("conditional",Call("empty")),Eq,V("M"));
        Formula ae=All("p",addr,All("F",Call("G"),Call("aeEq",V("M"),Call("pullback",p,f),Call("compose",f,pre))));
        Formula bound=All("p",addr,All("F",Call("G"),Seq(Norm(Call("pullback",p,f)),Leq,Mul(Call("pullbackBound",p),Norm(f)))));
        Formula trace=All("p",addr,All("z",Call("H"),Call("aeEq",V("M"),Call("conditionalTrace",p,z),Call("compose",Call("J",z),pre))));
        Formula inverse=All("p",addr,All("w",omega,Seq(Call("tail",Call("length",p),Call("prepend",p,w)),Eq,w)));
        return Seq(Par(positive),Land,Par(deletion),Land,Par(law),Land,Par(empty),Land,Par(ae),Land,Par(bound),Land,Par(trace),Land,Par(inverse));
    }
}
