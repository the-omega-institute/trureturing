using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class RebitExclusionDistanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/RebitExclusionDistance.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/elliott2025complex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The minimum average trace distance from the four-input exclusion distribution over all rebit strategies is exactly one twelfth.",
        H("The minimum distance for rebit exclusion strategies"),
        Blocks(
            Node("target", "The exclusion distribution", "target", TargetFormula(),
                "Section III.A uses four inputs and four outputs. The target probability is zero when the output equals the input and one third otherwise.",
                AssessedProvenance.FromLiterature(Source)),
            Node("strategy", "Real states and a real measurement", "IsRebitStrategy", StrategyFormula(),
                "A strategy consists of four real positive-semidefinite two by two states of trace one and four real positive-semidefinite measurement effects whose sum is the identity matrix. Over the real numbers, Matrix.PosSemidef includes symmetry. Mixed states cover Alice's private randomness, and positive-operator-valued measurements cover Bob's private randomness and post-processing, including the dilated measurement in Appendix D. The players have no shared randomness or correlations between rounds.",
                AssessedProvenance.FromLiterature(Source)),
            Node("dist", "The average trace distance", "dist", DistanceFormula(),
                "Section IV and Appendix D measure the error by averaging the trace distance between the target and realized output distributions over the four equally weighted inputs. For input x and output y, the realized probability is Matrix.trace of the product of the state and the effect. The factor one half gives the trace distance of the two distributions for each input.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "One twelfth is the attained minimum", "claim", ClaimFormula(),
                "Appendix D constructs a rebit strategy with average trace distance one twelfth and conjectures that this is the minimum. IsLeast states both that one twelfth belongs to the set of attained distances and that it is at most every element of that set. The set includes mixed states and every four-outcome real positive-operator-valued measurement.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("rebit-distance-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The minimum is exactly one twelfth"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The four real symmetric two by two states lie in a three-dimensional real vector space, so they are linearly dependent. Taking the trace of a nonzero linear relation shows that its coefficients sum to zero. Applying the trace against any effect makes the same relation vanish for the realized probabilities, whereas its value for the target probabilities is minus the corresponding coefficient divided by three.")),
                    Paragraph(Text(
                        "The triangle inequality bounds the absolute value of each coefficient divided by three by the largest absolute coefficient times the total error in the corresponding output column. A nonzero coefficient family with sum zero has L1 norm at least twice its largest absolute coefficient. Summing the column estimates therefore gives total absolute error at least two thirds, and the factors one fourth and one half give average trace distance at least one twelfth.")),
                    Paragraph(Text(
                        "An explicit strategy with square root of three attains the bound. Its first three input rows equal the target rows, while its fourth row repeats the third. The total absolute error is two thirds, so the average trace distance is one twelfth. This realizes the construction in Appendix D as a real positive-operator-valued measurement and proves the conjectured minimum."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("elliott-2025-rebit-minimum-distance"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("rebit-distance-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "QuantumBounds", "RebitExclusionDistance", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Fin(int size) => At(Qualified("Fin"), new Formula.Number(size));
    private static Formula MatrixType() => At(Qualified("Matrix"), Fin(2), Fin(2), Reals());
    private static Formula FamilyType() => Parenthesized(new Formula.TypeArrow(Fin(4), MatrixType()));
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Some(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalent(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Trace(Formula matrix) => At(Qualified("Matrix", "trace"), matrix);
    private static Formula PositiveSemidefinite(Formula matrix) => At(Qualified("Matrix", "PosSemidef"), matrix);
    private static Formula SumOver(string variable, Formula type, Formula summand) => Seq(
        new Formula.Subscript(Sum, Seq(X(variable), Colon, Sp, type)), Sp, Parenthesized(summand));
    private static Formula Families(Formula body) => All("rho", FamilyType(), All("E", FamilyType(), body));

    private static Formula TargetFormula() => All("x", Fin(4), All("y", Fin(4),
        Equal(LocalCall("target", X("x"), X("y")), Parenthesized(Seq(
            F.Text, Grp(X("if")), Sp, Equal(X("x"), X("y")), Sp,
            F.Text, Grp(X("then")), Sp, D(0), Sp,
            F.Text, Grp(X("else")), Sp, new Formula.Fraction(D(1), D(3)))))));

    private static Formula StrategyFormula()
    {
        Formula states = All("x", Fin(4), And(
            PositiveSemidefinite(At(X("rho"), X("x"))),
            Equal(Trace(At(X("rho"), X("x"))), D(1))));
        Formula effects = All("y", Fin(4), PositiveSemidefinite(At(X("E"), X("y"))));
        Formula normalization = Equal(SumOver("y", Fin(4), At(X("E"), X("y"))), D(1));
        return Families(Equivalent(LocalCall("IsRebitStrategy", X("rho"), X("E")),
            And(states, And(effects, normalization))));
    }

    private static Formula DistanceFormula()
    {
        Formula error = new Formula.Absolute(Subtract(LocalCall("target", X("x"), X("y")),
            Trace(Multiply(At(X("rho"), X("x")), At(X("E"), X("y"))))));
        Formula distance = Multiply(new Formula.Fraction(D(1), D(4)),
            SumOver("x", Fin(4), Multiply(new Formula.Fraction(D(1), D(2)), SumOver("y", Fin(4), error))));
        return Families(Equal(LocalCall("dist", X("rho"), X("E")), distance));
    }

    private static Formula ClaimFormula()
    {
        Formula attained = Some("rho", FamilyType(), Some("E", FamilyType(), And(
            LocalCall("IsRebitStrategy", X("rho"), X("E")),
            Equal(X("d"), LocalCall("dist", X("rho"), X("E"))))));
        Formula distances = Seq(OpenBrace, X("d"), Colon, Sp, Reals(), Sp, Mid, Sp, attained, Sp, CloseBrace);
        return Equivalent(Local("claim"), At(Qualified("IsLeast"), distances,
            new Formula.Fraction(D(1), D(1, 2))));
    }
}
