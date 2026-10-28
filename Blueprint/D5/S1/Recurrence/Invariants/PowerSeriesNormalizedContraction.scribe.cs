using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class PowerSeriesNormalizedContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict improvement of coefficient agreement gives a unique normalized formal power-series fixed point.", H("Normalized coefficient contractions"),
        Blocks(
            Node("exists_unique_fixed", "A normalized contraction has a unique fixed point",
                Disp(Seq(Forall, Sp, F.Id("R"), Colon, Sp, F.Id("Type"), Comma, Sp, Seq(OpenBracket, Call("CommRing", F.Id("R")), CloseBracket, Comma, Sp, Seq(Forall, Sp, F.Id("step"), Colon, Sp, new Formula.TypeArrow(Call("PowerSeries", F.Id("R")), Call("PowerSeries", F.Id("R"))), Comma, Sp, Seq(Parenthesized(Seq(Forall, Sp, F.Id("f"), Colon, Sp, Call("PowerSeries", F.Id("R")), Comma, Sp, Seq(Parenthesized(Seq(Call("constantCoeff", F.Id("f")), Sp, Eq, Sp, D(1))), Sp, Implies, Sp, Parenthesized(Seq(Call("constantCoeff", Call("step", F.Id("f"))), Sp, Eq, Sp, D(1)))))), Sp, Implies, Sp, Parenthesized(Seq(Parenthesized(Seq(Forall, Sp, F.Id("d"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Forall, Sp, F.Id("f"), Colon, Sp, Call("PowerSeries", F.Id("R")), Comma, Sp, Seq(Forall, Sp, F.Id("g"), Colon, Sp, Call("PowerSeries", F.Id("R")), Comma, Sp, Seq(Parenthesized(Seq(D(1), Sp, Le, Sp, F.Id("d"))), Sp, Implies, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("constantCoeff", F.Id("f")), Sp, Eq, Sp, D(1))), Sp, Implies, Sp, Parenthesized(Seq(Parenthesized(Seq(Call("constantCoeff", F.Id("g")), Sp, Eq, Sp, D(1))), Sp, Implies, Sp, Parenthesized(Seq(Parenthesized(Call("Agree", F.Id("d"), F.Id("f"), F.Id("g"))), Sp, Implies, Sp, Parenthesized(Call("Agree", new Formula.Binary(Parenthesized(F.Id("d")), FormulaBinaryOperator.Add, Parenthesized(D(1))), Call("step", F.Id("f")), Call("step", F.Id("g"))))))))))))))), Sp, Implies, Sp, Parenthesized(Seq(Exists, Sp, F.Id("f"), Colon, Sp, Call("PowerSeries", F.Id("R")), Comma, Sp, Seq(Parenthesized(Seq(Call("constantCoeff", F.Id("f")), Sp, Eq, Sp, D(1))), Sp, Land, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("f"), Sp, Eq, Sp, Call("step", F.Id("f")))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("g"), Colon, Sp, Call("PowerSeries", F.Id("R")), Comma, Sp, Seq(Parenthesized(Seq(Call("constantCoeff", F.Id("g")), Sp, Eq, Sp, D(1))), Sp, Implies, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("g"), Sp, Eq, Sp, Call("step", F.Id("g")))), Sp, Implies, Sp, Parenthesized(Seq(F.Id("g"), Sp, Eq, Sp, F.Id("f")))))))))))))))))))),
                "The nth coefficient is read from the nth iterate. Improving agreement stabilizes these coefficients; induction proves the fixed-point identity and uniqueness.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("geometric_zero", "Geometric zero",
                Disp(Seq(Forall, Sp, F.Id("R"), Colon, Sp, F.Id("Type"), Comma, Sp, Seq(OpenBracket, Call("CommRing", F.Id("R")), CloseBracket, Comma, Sp, Seq(Call("constantCoeff", Parenthesized(Seq(Call("geometric"), Colon, Sp, Call("PowerSeries", F.Id("R"))))), Sp, Eq, Sp, D(0))))),
                "The geometric series X times mk 1 has constant coefficient zero.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("geometric_one", "Geometric one",
                Disp(Seq(Forall, Sp, F.Id("R"), Colon, Sp, F.Id("Type"), Comma, Sp, Seq(OpenBracket, Call("CommRing", F.Id("R")), CloseBracket, Comma, Sp, Seq(Call("coeff", D(1), Parenthesized(Seq(Call("geometric"), Colon, Sp, Call("PowerSeries", F.Id("R"))))), Sp, Eq, Sp, D(1))))),
                "The coefficient of X in X times mk 1 is one.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("geometric_coeff", "Geometric coeff",
                Disp(Seq(Forall, Sp, F.Id("R"), Colon, Sp, F.Id("Type"), Comma, Sp, Seq(OpenBracket, Call("CommRing", F.Id("R")), CloseBracket, Comma, Sp, Seq(Forall, Sp, F.Id("n"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Parenthesized(Seq(D(1), Sp, Le, Sp, F.Id("n"))), Sp, Implies, Sp, Parenthesized(Seq(Call("coeff", F.Id("n"), Parenthesized(Seq(Call("geometric"), Colon, Sp, Call("PowerSeries", F.Id("R"))))), Sp, Eq, Sp, D(1)))))))),
                "Every positive coefficient of the geometric series is one.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("geometric_mul", "Geometric mul",
                Disp(Seq(Forall, Sp, F.Id("R"), Colon, Sp, F.Id("Type"), Comma, Sp, Seq(OpenBracket, Call("CommRing", F.Id("R")), CloseBracket, Comma, Sp, Seq(new Formula.Binary(Parenthesized(Parenthesized(Seq(Call("geometric"), Colon, Sp, Call("PowerSeries", F.Id("R"))))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(D(1)), FormulaBinaryOperator.Subtract, Parenthesized(F.Id("X"))))), Sp, Eq, Sp, F.Id("X"))))),
                "Multiplying the geometric series by one minus X gives X.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("map_subst_pow", "Map subst pow",
                Disp(Seq(Forall, Sp, F.Id("R"), Colon, Sp, F.Id("Type"), Comma, Sp, Seq(OpenBracket, Call("CommRing", F.Id("R")), CloseBracket, Comma, Sp, Seq(Forall, Sp, F.Id("S"), Colon, Sp, F.Id("Type"), Comma, Sp, Seq(OpenBracket, Call("CommRing", F.Id("S")), CloseBracket, Comma, Sp, Seq(Forall, Sp, F.Id("hom"), Colon, Sp, Seq(F.Id("R"), Sp, new Formula.Power(To, Seq(Plus, Star)), Sp, F.Id("S")), Comma, Sp, Seq(Forall, Sp, F.Id("f"), Colon, Sp, Call("PowerSeries", F.Id("R")), Comma, Sp, Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Parenthesized(Seq(F.Id("k"), Sp, Neq, Sp, D(0))), Sp, Implies, Sp, Parenthesized(Seq(Call("map", F.Id("hom"), Call("subst", new Formula.Power(Parenthesized(F.Id("X")), F.Id("k")), F.Id("f"))), Sp, Eq, Sp, Call("subst", new Formula.Power(Parenthesized(F.Id("X")), F.Id("k")), Call("map", F.Id("hom"), F.Id("f")))))))))))))),
                "Mapping coefficients along a ring homomorphism commutes with substitution by a positive power of X.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("geometric_subst_mul", "Geometric subst mul",
                Disp(Seq(Forall, Sp, F.Id("R"), Colon, Sp, F.Id("Type"), Comma, Sp, Seq(OpenBracket, Call("CommRing", F.Id("R")), CloseBracket, Comma, Sp, Seq(Forall, Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Parenthesized(Seq(F.Id("k"), Sp, Neq, Sp, D(0))), Sp, Implies, Sp, Parenthesized(Seq(new Formula.Binary(Parenthesized(Call("subst", new Formula.Power(Parenthesized(F.Id("X")), F.Id("k")), Parenthesized(Seq(Call("geometric"), Colon, Sp, Call("PowerSeries", F.Id("R")))))), FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Binary(Parenthesized(D(1)), FormulaBinaryOperator.Subtract, Parenthesized(new Formula.Power(Parenthesized(F.Id("X")), F.Id("k")))))), Sp, Eq, Sp, new Formula.Power(Parenthesized(F.Id("X")), F.Id("k"))))))))),
                "Substituting X to a positive power in the geometric identity preserves multiplication.", DescribeRole.Theorem, AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("powerseriesnormalizedcontraction-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        arguments.Length == 0 ? Named(name) : new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
