using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class FiniteCouplingPushforwardLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/CausalMoments/FiniteCouplingPushforwardLift.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lift a coarse rational coupling to the original carriers while preserving every original marginal and every paired-readout query.", H("FiniteCouplingPushforwardLift"), Blocks(
            Paragraph(Text("X, Y, A and B are finite types, with decidable equality on A and B. left and right are FiniteResponseLaw values on X and Y. f : X to A, g : Y to B, and joint is a law on A times B. The parameters hl and hr denote exactly the two displayed coarse-marginal equalities. The lifted result is a law on X times Y. All scalar operations are rational, including total division by zero; validity on null fibers is proved separately.")),
            Describe.Lean(DescribeId.Create("lifted-coupling-mass"), DeclarationHandle.Create(Prefix + "liftedCouplingMass"),
                H("Explicit disaggregation weights"), StatementSource.FromAuthor(Disp(All("X Y A B left right f g joint x y", B(C("liftedCouplingMass", V("left"), V("right"), V("f"), V("g"), V("joint"), C("pair", V("x"), V("y"))), Eq, B(B(C("mass", V("joint"), C("pair", C("apply", V("f"), V("x")), C("apply", V("g"), V("y")))), Cdot, Divide(C("mass", V("left"), V("x")), C("mass", C("pushforwardResponseLaw", V("left"), V("f")), C("apply", V("f"), V("x"))))), Cdot, Divide(C("mass", V("right"), V("y")), C("mass", C("pushforwardResponseLaw", V("right"), V("g")), C("apply", V("g"), V("y"))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each original atom receives its coarse cell mass times its two within-fiber shares. Null coarse marginals force the corresponding coarse cells to vanish."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lift-coarse-coupling"), DeclarationHandle.Create(Prefix + "liftCoarseCoupling"),
                H("Normalize the original-carrier law"), StatementSource.FromAuthor(Disp(All("X Y A B left right f g joint hl hr", B(And(All("a", B(C("leftResponseMarginal", C("mass", V("joint")), V("a")), Eq, C("mass", C("pushforwardResponseLaw", V("left"), V("f")), V("a")))), All("b", B(C("rightResponseMarginal", C("mass", V("joint")), V("b")), Eq, C("mass", C("pushforwardResponseLaw", V("right"), V("g")), V("b"))))), Rightarrow, B(C("mass", C("liftCoarseCoupling", V("left"), V("right"), V("f"), V("g"), V("joint"), V("hl"), V("hr"))), Eq, C("liftedCouplingMass", V("left"), V("right"), V("f"), V("g"), V("joint"))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The definition supplies nonnegativity and total mass one from the exact two coarse-marginal contracts, without a strict-positivity premise."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lift-coarse-coupling-marginals"), DeclarationHandle.Create(Prefix + "liftCoarseCoupling_marginals"),
                H("Preserve every original probability"), StatementSource.FromAuthor(Disp(All("X Y A B left right f g joint hl hr", B(And(All("a", B(C("leftResponseMarginal", C("mass", V("joint")), V("a")), Eq, C("mass", C("pushforwardResponseLaw", V("left"), V("f")), V("a")))), All("b", B(C("rightResponseMarginal", C("mass", V("joint")), V("b")), Eq, C("mass", C("pushforwardResponseLaw", V("right"), V("g")), V("b"))))), Rightarrow, And(All("x", B(C("leftResponseMarginal", C("mass", C("liftCoarseCoupling", V("left"), V("right"), V("f"), V("g"), V("joint"), V("hl"), V("hr"))), V("x")), Eq, C("mass", V("left"), V("x")))), All("y", B(C("rightResponseMarginal", C("mass", C("liftCoarseCoupling", V("left"), V("right"), V("f"), V("g"), V("joint"), V("hl"), V("hr"))), V("y")), Eq, C("mass", V("right"), V("y"))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The entire original marginal vectors are retained, including zero-probability states."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lift-coarse-coupling-expectation"), DeclarationHandle.Create(Prefix + "liftCoarseCoupling_expectation"),
                H("Preserve all paired-readout expectations"), StatementSource.FromAuthor(Disp(All("X Y A B left right f g joint hl hr query", B(And(All("a", B(C("leftResponseMarginal", C("mass", V("joint")), V("a")), Eq, C("mass", C("pushforwardResponseLaw", V("left"), V("f")), V("a")))), All("b", B(C("rightResponseMarginal", C("mass", V("joint")), V("b")), Eq, C("mass", C("pushforwardResponseLaw", V("right"), V("g")), V("b"))))), Rightarrow, B(C("linearObjective", Lam("pair", C("apply", V("query"), C("pair", C("apply", V("f"), C("fst", V("pair"))), C("apply", V("g"), C("snd", V("pair")))))), C("mass", C("liftCoarseCoupling", V("left"), V("right"), V("f"), V("g"), V("joint"), V("hl"), V("hr")))), Eq, C("linearObjective", V("query"), C("mass", V("joint")))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("query is an arbitrary rational function on A times B, chosen after the lift. Its expectation equals that under the supplied coarse coupling."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula B(Formula x, Formula op, Formula y) => Seq(P(x), Sp, op, Sp, P(y));
    private static Formula All(string names, Formula body) => Quantify(Forall, names, body);
    private static Formula Lam(string names, Formula body) => Quantify(LambdaLower, names, body);
    private static Formula Divide(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Quantify(Formula q, string names, Formula body)
    {
        var xs = new List<Formula> { q, Sp };
        foreach (var name in names.Split(' ')) xs.AddRange([V(name), Comma, Sp]);
        xs.Add(body); return Seq([.. xs]);
    }
    private static Formula And(params Formula[] values)
    {
        var xs = new List<Formula>();
        for (var i = 0; i < values.Length; i++)
        { if (i > 0) xs.AddRange([Sp, Land, Sp]); xs.Add(P(values[i])); }
        return Seq([.. xs]);
    }
    private static Formula C(string name, params Formula[] values)
    {
        var xs = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < values.Length; i++)
        { if (i > 0) xs.AddRange([Comma, Sp]); xs.Add(values[i]); }
        xs.Add(Close); return Seq([.. xs]);
    }
}
