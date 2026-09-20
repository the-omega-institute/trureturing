using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class ZeckendorfTwoReadTomographyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Arith/ZeckendorfTwoReadTomography.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two correlated cumulative-residue tests recover each mass on the arithmetic future quotient.",
        H("Two-Read Tomography of Zeckendorf Probability States"),
        Blocks(
            Paragraph(Text("The coefficient ring is ZMod M with M positive, including composite "
                + "moduli. Every indexed weight row has an explicit Bezout certificate. "
                + "Distinct chosen projective representatives have nonzero determinant; "
                + "the determinant is not assumed to be a unit.")),
            Describe.Lean(DescribeId.Create("zk-two-read-first-residual"),
                DeclarationHandle.Create(Owner + "firstResidual"), H("First cumulative residue"),
                StatementSource.FromAuthor(FirstFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("To target residue r, use the coefficient pair (-r*e,-r*f). "
                    + "At candidate residue rp and row (up,vp), the resulting residue is "
                    + "rp-r*(e*up+f*vp). The earlier guarded-word construction realizes this "
                    + "pair with a legal word and returns the weight clock."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zk-two-read-second-residual"),
                DeclarationHandle.Create(Owner + "secondResidual"), H("Second cumulative residue without reset"),
                StatementSource.FromAuthor(SecondFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The next coefficient pair is (v,-u), formed from the "
                    + "target row. Its contribution v*up-u*vp is added to the first residue. "
                    + "The first reading does not erase the accumulator or prepare a new state."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zk-two-read-point-mass-recovery"),
                DeclarationHandle.Create(Owner + "result"), H("Explicit separation and exact finite-mass recovery"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every finite indexed family of unimodular rows with "
                        + "the displayed separation property, and every target index d and "
                        + "residue r, both tests vanish on a unimodular candidate exactly "
                        + "when one unit scales its entire triple from the target triple. "
                        + "The proof constructs this scalar and its inverse from the two "
                        + "Bezout certificates; no field instance or target equivalence is assumed.")),
                    Paragraph(Text("On distinct projective representatives this joint event "
                        + "is exactly i=d and rp=r. Summing it against any real signed "
                        + "mass mu therefore returns mu(d,r). Nonnegative normalized "
                        + "probabilities are included without adding an assumption needed "
                        + "only for their interpretation.")),
                    Paragraph(Text("The experiment family has one designed pair per target. "
                        + "Learning its joint probabilities requires repeated samples or "
                        + "other statistical information. Two observed bits do not encode "
                        + "a whole probability distribution. The complete finite-word "
                        + "implementation and the prime-power terminal-rank calculation "
                        + "are ordinary proofs in the existing golden-interface note; "
                        + "this declaration certifies the modular separating events and sums.")),
                    Paragraph(Text("Predictive-state and finite Radon-transform background "
                        + "is recorded in Library/notes/singh2004zeckendorfprobability.md: "
                        + "Singh-James-Rudary (UAI2004), Kingston (2006), and Ben-Ari-Miller. "
                        + "Those works are background, not sources of this exact theorem. This is not a "
                        + "claim of an integer Wall-Sun-Sun witness or an independently "
                        + "proved restriction on its initial-depth zero set."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), a);
    private static Formula R() => C("ZMod", V("M"));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula All(string s, Formula type, Formula body) => Seq(Forall, Sp, V(s), Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula Ex(string s, Formula type, Formula body) => Seq(Exists, Sp, V(s), Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula Many(string[] names, Formula type, Formula body)
    { for (var j=names.Length-1;j>=0;--j) body=All(names[j],type,body); return body; }
    private static Formula And(params Formula[] xs)
    { var r=xs[^1]; for(var j=xs.Length-2;j>=0;--j) r=C("And",xs[j],r); return r; }
    private static Formula At(string f, Formula i) => C(f,i);
    private static Formula First(Formula e, Formula f, Formula rp, Formula up, Formula vp) =>
        C("firstResidual",V("r"),e,f,rp,up,vp);
    private static Formula Second(Formula u, Formula v, Formula e, Formula f, Formula rp, Formula up, Formula vp) =>
        C("secondResidual",V("r"),u,v,e,f,rp,up,vp);
    private static Formula FirstFormula() => Disp(Many(new[]{"r","e","f","rp","up","vp"},R(),
        Eqn(First(V("e"),V("f"),V("rp"),V("up"),V("vp")),
            Sub(V("rp"),Mul(V("r"),Add(Mul(V("e"),V("up")),Mul(V("f"),V("vp"))))))));
    private static Formula SecondFormula() => Disp(Many(new[]{"r","u","v","e","f","rp","up","vp"},R(),
        Eqn(Second(V("u"),V("v"),V("e"),V("f"),V("rp"),V("up"),V("vp")),
            Sub(Add(First(V("e"),V("f"),V("rp"),V("up"),V("vp")),Mul(V("v"),V("up"))),Mul(V("u"),V("vp"))))));
    private static Formula Event(Formula rp, Formula up, Formula vp) => And(
        Eqn(First(At("E",V("d")),At("F",V("d")),rp,up,vp),D(0)),
        Eqn(Second(At("U",V("d")),At("V",V("d")),At("E",V("d")),At("F",V("d")),rp,up,vp),D(0)));
    private static Formula ResultFormula()
    {
        var i=V("i"); var j=V("j"); var d=V("d");
        var rows=All("i",V("I"),Eqn(Add(Mul(At("E",i),At("U",i)),Mul(At("F",i),At("V",i))),D(1)));
        var separate=Many(new[]{"i","j"},V("I"),C("Implies",C("Not",Eqn(i,j)),
            C("Not",Eqn(Sub(Mul(At("V",i),At("U",j)),Mul(At("U",i),At("V",j))),D(0)))));
        var scaled=Ex("a",R(),Ex("aInv",R(),And(Eqn(Mul(V("a"),V("aInv")),D(1)),
            Eqn(V("rp"),Mul(V("a"),V("r"))),Eqn(V("up"),Mul(V("a"),At("U",d))),Eqn(V("vp"),Mul(V("a"),At("V",d))))));
        var pair=Many(new[]{"rp","up","vp","ep","fp"},R(),C("Implies",
            Eqn(Add(Mul(V("ep"),V("up")),Mul(V("fp"),V("vp"))),D(1)),
            C("Iff",Event(V("rp"),V("up"),V("vp")),scaled)));
        var summand=C("ite",Event(V("rp"),At("U",i),At("V",i)),C("mu",i,V("rp")),D(0));
        var mass=All("mu",C("Function",V("I"),C("Function",R(),C("Real"))),
            Eqn(C("sum",V("I"),C("lambda",i,C("sum",R(),C("lambda",V("rp"),summand)))),C("mu",d,V("r"))));
        return Disp(All("M",Seq(Mathbb,Grp(V("N"))),C("Implies",C("NeZero",V("M")),
            All("I",C("Type"),C("Implies",C("Fintype",V("I")),
                Many(new[]{"U","V","E","F"},C("Function",V("I"),R()),
                    All("d",V("I"),All("r",R(),C("Implies",And(rows,separate),And(pair,mass))))))))));
    }
}
