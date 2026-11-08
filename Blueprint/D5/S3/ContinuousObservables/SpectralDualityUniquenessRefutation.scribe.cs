using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class SpectralDualityUniquenessRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/ContinuousObservables/SpectralDualityUniquenessRefutation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/vegacoso2026spectraldualityrigidity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An open family of two-site amplitudes refutes generic global uniqueness in the range N ≤ m.",
        H("Generic global uniqueness fails in the range N ≤ m"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("vega-coso-global-uniqueness-extension-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The global uniqueness extension"),
                StatementSource.FromAuthor(Disp(Equal(Typed(Q("claim"), Q("Prop")),
                    Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Section 9, page 18, states: “Likewise, Proposition 4.16 is proved for N > m, "
                        + "and the case N ≤ m is open.” The proposition on page 11 states: "
                        + "“In the setting of Proposition 4.15, assume moreover N > m and (H1). "
                        + "Then there is an open dense subset 𝒢 ⊂ 𝒟, whose complement has Lebesgue measure "
                        + "zero, such that for every D ∈ 𝒢 for which (A, B = βA + D) satisfies (H2), "
                        + "the distribution π is the only insensitive distribution of (A, B), at any level.”")),
                    Paragraph(Text(
                        "The displayed assertion asks for the same global uniqueness in the range N ≤ m, "
                        + "with N,m ≥ 2, entrywise positive A, an interior probability vector π, β > 0, "
                        + "and linearly independent real functions f on (0,1). It asks only for an open "
                        + "dense set, omitting the additional null-complement condition. Indices ν and z "
                        + "run over Fin N and Fin m. The subtype of matrices D satisfying D.mulVec π = 0 "
                        + "has its induced topology. Each displayed finite sum ranges over the indicated Fin type.")),
                    Paragraph(Text(
                        "Page 4 defines u_z(γ) = ∑ν f_ν(γ) A_ν(z), "
                        + "s_z(γ) = ∑ν f_ν(γ) [A_ν(z) + B_ν(z)], and "
                        + "C(π,γ) = ⟨π,u(γ)⟩/⟨π,s(γ)⟩, with ⟨π,x⟩ = ∑z π_z x_z. "
                        + "Definition 2.2, page 5, states: “A distribution π ∈ Δ̄ is insensitive at level c "
                        + "if C(π,γ) = c for every γ ∈ (0,1).” The expanded assertion substitutes "
                        + "B_ν(z) = β A_ν(z) + D_ν(z) into these expressions. The variable π′ ranges "
                        + "over the closed simplex and c over all real numbers; (H2) requires each "
                        + "s_z(γ) to be positive. The source poses this range as an open question, "
                        + "rather than asserting the extension as a theorem."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("vega-coso-global-uniqueness-extension-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A nonempty open set of two-site counterexamples"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take N=m=2, A=[[1,2],[2,1]], π=(1/2,1/2), β=1 and f(γ)=(1,γ). "
                        + "Every matrix in D.mulVec π = 0 has the form D=[[a,−a],[b,−b]]. "
                        + "The strict inequalities 0<a<1, 0<b<1, a/2<b<2a and a≠b define a "
                        + "nonempty relatively open subset of that entire matrix space. For each of "
                        + "these matrices, q=((2b−a)/(a+b),(2a−b)/(a+b)) is an interior probability "
                        + "vector distinct from π, and D.mulVec q=(b−a) • A.mulVec q. Consequently "
                        + "C(q,γ)=1/(2+b−a) for every γ∈(0,1), while all s_z(γ) are positive. "
                        + "Every dense subset meets this open set and therefore contains a failure "
                        + "of global uniqueness. This refutes the universal extension; the published "
                        + "N>m proposition and the strict N<m case are separate statements."))),
                DescribeRole.Theorem))));

    private static Formula ClaimBody()
    {
        Formula matrix = MatrixType();
        Formula vector = new Formula.TypeArrow(FinType(X("m")), Reals());
        Formula space = Seq(OpenBrace, Typed(X("D"), matrix), Sp, Mid, Sp,
            Equal(App(Q("Matrix", "mulVec"), X("D"), X("pi")), D(0)), CloseBrace);
        Formula positive = All("nu", FinType(X("N")), All("z", FinType(X("m")),
            LT(D(0), App(X("A"), X("nu"), X("z")))));
        Formula interior = And(
            All("z", FinType(X("m")), LT(D(0), App(X("pi"), X("z")))),
            Equal(SumOver("z", X("m"), App(X("pi"), X("z"))), D(1)));
        Formula h2 = All("z", FinType(X("m")), All("gamma", Parameter(),
            LT(D(0), SpectralSum(true))));
        Formula distribution = And(
            All("z", FinType(X("m")), LE(D(0), App(X("other"), X("z")))),
            Equal(SumOver("z", X("m"), App(X("other"), X("z"))), D(1)));
        Formula insensitive = All("gamma", Parameter(), Equal(
            new Formula.Fraction(
                SumOver("z", X("m"), Multiply(App(X("other"), X("z")), SpectralSum(false))),
                SumOver("z", X("m"), Multiply(App(X("other"), X("z")), SpectralSum(true)))),
            X("c")));
        Formula unique = All("D", space, Imp(Member(X("D"), X("G")), Imp(h2,
            All("other", vector, All("c", Reals(), Imp(distribution,
                Imp(insensitive, Equal(X("other"), X("pi")))))))));
        Formula generic = Some("G", App(Q("Set"), space), And(App(Q("IsOpen"), X("G")),
            And(App(Q("Dense"), X("G")), unique)));
        Formula body = Imp(App(Q("LinearIndependent"), Reals(), X("f")), generic);
        body = Imp(LT(D(0), X("beta")), body);
        body = Imp(interior, body);
        body = Imp(positive, body);
        body = Imp(LE(X("N"), X("m")), body);
        body = Imp(LE(D(2), X("m")), body);
        body = Imp(LE(D(2), X("N")), body);
        body = All("f", new Formula.TypeArrow(FinType(X("N")),
            new Formula.TypeArrow(Parameter(), Reals())), body);
        body = All("beta", Reals(), body);
        body = All("pi", vector, body);
        body = All("A", matrix, body);
        return All("N", Naturals(), All("m", Naturals(), body));
    }

    private static Formula SpectralSum(bool denominator)
    {
        Formula amplitude = App(X("A"), X("nu"), X("z"));
        Formula entry = Seq(X("D"), Dot, D(1));
        Formula value = denominator ? Add(amplitude, Parenthesized(Add(
            Multiply(X("beta"), amplitude), App(entry, X("nu"), X("z"))))) : amplitude;
        return SumOver("nu", X("N"), Multiply(App(X("f"), X("nu"), X("gamma")), value));
    }

    private static Formula MatrixType() => App(Q("Matrix"), FinType(X("N")), FinType(X("m")), Reals());
    private static Formula Parameter() => App(Q("Set", "Ioo"), Typed(D(0), Reals()), D(1));
    private static Formula FinType(Formula size) => App(Q("Fin"), size);
    private static Formula SumOver(string variable, Formula size, Formula body) =>
        Seq(Sum, Underscore, Grp(Typed(X(variable), FinType(size))), Sp, Parenthesized(body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula LT(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LE(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Multiply(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula X(string name) => name switch
    {
        "pi" => Pi,
        "other" => Seq(Pi, Apos),
        "beta" => Beta,
        "gamma" => GammaLower,
        "nu" => Nu,
        _ => F.Id(name),
    };
    private static Formula Q(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
}
