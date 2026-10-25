using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class ConditionallyRandomUniformAttenuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/QuantumContext/gudder2021mutuallyunbiasedobservables");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional randomness implies uniform attenuation for all finite quantum observables.",
        H("Conditional randomness and uniform attenuation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conditioned"),
                DeclarationHandle.Create(Prefix + "conditioned"),
                H("The conditioned matrix family"),
                StatementSource.FromAuthor(Disp(ConditionedFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For finite complex matrix families A and B, the conditioned matrix at outcome y "
                        + "is the unread operation on B y with operators CFC.sqrt (A x). "
                        + "This operation sums K x * B y * K x over x. "
                        + "For positive effects the square roots are Hermitian, so this is the sum of the sequential products A x ∘ B y. "
                        + "Gudder defines the sequential product in the arXiv v1 TeX at line 97 "
                        + "and the conditioned observable at lines 117–120."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("uniform-attenuation"),
                DeclarationHandle.Create(Prefix + "UniformAttenuation"),
                H("Uniform attenuation in both orders"),
                StatementSource.FromAuthor(Disp(UniformAttenuationFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every outcome x of A and y of B, measuring B y after A x gives A x divided by n, "
                        + "and measuring A x after B y gives B y divided by m. "
                        + "The operation luders E F is CFC.sqrt E * F * CFC.sqrt E. "
                        + "This is Condition (1) in Gudder's arXiv v1 TeX, lines 174–182. "
                        + "The natural numbers n and m are explicitly cast to complex scalars before division. "
                        + "The predicate itself applies to arbitrary matrix families; positivity and normalization are separate conditions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conditionally-random"),
                DeclarationHandle.Create(Prefix + "ConditionallyRandom"),
                H("Conditional randomness in both orders"),
                StatementSource.FromAuthor(Disp(ConditionallyRandomFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Each conditioned outcome of B given A is the identity matrix divided by n, "
                        + "and each conditioned outcome of A given B is the identity matrix divided by m. "
                        + "For observables, this means that both conditioned observables have uniform outcome probabilities in every state. "
                        + "This is Condition (2) in Gudder's arXiv v1 TeX, lines 174–182. "
                        + "The displayed predicate places no positivity or normalization condition on A or B."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The converse for arbitrary finite observables"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural dimension d and positive outcome counts m and n, "
                        + "two positive operator valued measures that are conditionally random uniformly attenuate each other. "
                        + "Here IsPOVM means that every matrix in the family is positive semidefinite and the family sums to the identity. "
                        + "No projection or sharpness condition is imposed, and dimension zero is included. "
                        + "This is the converse of Theorem 2.1(i), stated in Gudder's arXiv v1 TeX at lines 184–186; "
                        + "the question at line 223 asks whether this converse holds. "
                        + "The separate question concerning the converse of part (ii) is not asserted here."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Conditional randomness forces uniform attenuation"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First let K be positive semidefinite and X Hermitian. Set R = CFC.sqrt K. "
                            + "Then R is Hermitian, R * R = K, and R * X * R is Hermitian. "
                            + "Cyclicity of the trace, followed by substitution of R * R for K, gives "
                            + "trace (X * (K * X * K)) = trace ((R * X * R).conjTranspose * (R * X * R)). "
                            + "The right side is nonnegative because it is the trace of a matrix of the form Y.conjTranspose * Y.")),
                    Paragraph(Text(
                        "Next let K be a finite family of positive semidefinite matrices and suppose that "
                            + "the sum of K x * X * K x over x is zero. Multiply this equality on the left by X and take the trace. "
                            + "Linearity gives a sum of the preceding nonnegative traces equal to zero, so every trace is zero. "
                            + "For each x, trace (Y.conjTranspose * Y) = 0 implies Y = 0, "
                            + "with Y = CFC.sqrt (K x) * X * CFC.sqrt (K x). "
                            + "Multiplying this zero matrix on both sides by CFC.sqrt (K x) gives K x * X * K x = 0.")),
                    Paragraph(Text(
                        "Now let A be a positive operator valued measure, B a Hermitian matrix, and c a self-adjoint complex scalar. "
                            + "Suppose the sum of luders (A x) B over x is c times the identity. "
                            + "The identity CFC.sqrt (A x) * CFC.sqrt (A x) = A x shows that "
                            + "CFC.sqrt (A x) * (B − c • 1) * CFC.sqrt (A x) = luders (A x) B − c • A x. "
                            + "Summing and using the normalization of A makes this sum zero. "
                            + "The matrix B − c • 1 is Hermitian, and every CFC.sqrt (A x) is positive semidefinite. "
                            + "Apply the preceding conclusion with K x = CFC.sqrt (A x) and X = B − c • 1. "
                            + "Every centered summand vanishes, hence luders (A x) B = c • A x for every x.")),
                    Paragraph(Text(
                        "Finally fix d, m, n, A and B satisfying the displayed hypotheses. "
                            + "For each y, the first conditional-randomness equality supplies the required sum for the observable A, "
                            + "the Hermitian matrix B y and the self-adjoint scalar c = 1 / (n : ℂ). "
                            + "It follows that luders (A x) (B y) = (1 / (n : ℂ)) • A x for every x. "
                            + "Exchange A and B and use the second conditional-randomness equality with c = 1 / (m : ℂ) "
                            + "to obtain luders (B y) (A x) = (1 / (m : ℂ)) • B y. "
                            + "These are the two required identities for every x and y."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gudder-2021-conditionally-random-uniform-attenuation"),
                    ResolutionKind.Proved)))));

    private static Formula ConditionedFormula() => Families(All("y", FinOf(X("n")),
        Equal(Typed(LocalCall("conditioned", X("A"), X("B"), X("y")), MatrixType()),
            At(Qualified("D5", "S3", "Observer", "Conditioning", "unreadState"),
                LambdaOf("x", FinOf(X("m")), At(Qualified("CFC", "sqrt"), At(X("A"), X("x")))),
                At(X("B"), X("y"))))));

    private static Formula UniformAttenuationFormula() => Families(Equivalence(
        LocalCall("UniformAttenuation", X("A"), X("B")),
        All("x", FinOf(X("m")), All("y", FinOf(X("n")), Conjunction(
            Equal(Luders(At(X("A"), X("x")), At(X("B"), X("y"))),
                Smul(Reciprocal("n"), At(X("A"), X("x")))),
            Equal(Luders(At(X("B"), X("y")), At(X("A"), X("x"))),
                Smul(Reciprocal("m"), At(X("B"), X("y")))))))));

    private static Formula ConditionallyRandomFormula() => Families(Equivalence(
        LocalCall("ConditionallyRandom", X("A"), X("B")), Conjunction(
            All("y", FinOf(X("n")), Equal(LocalCall("conditioned", X("A"), X("B"), X("y")),
                Smul(Reciprocal("n"), Typed(D(1), MatrixType())))),
            All("x", FinOf(X("m")), Equal(LocalCall("conditioned", X("B"), X("A"), X("x")),
                Smul(Reciprocal("m"), Typed(D(1), MatrixType())))))));

    private static Formula ClaimBody() => Families(Arrow(Less(Typed(D(0), Naturals()), X("m")),
        Arrow(Less(Typed(D(0), Naturals()), X("n")),
            Arrow(IsPOVM(X("A")), Arrow(IsPOVM(X("B")),
                Arrow(LocalCall("ConditionallyRandom", X("A"), X("B")),
                    LocalCall("UniformAttenuation", X("A"), X("B"))))))));

    private static Formula Families(Formula body) => All("d", Naturals(), All("m", Naturals(),
        All("n", Naturals(), All("A", FamilyType("m"), All("B", FamilyType("n"), body)))));
    private static Formula FamilyType(string size) => Arrow(FinOf(X(size)), MatrixType());
    private static Formula MatrixType() => At(Qualified("Matrix"), FinOf(X("d")), FinOf(X("d")), Complexes());
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula Reciprocal(string size) => new Formula.Fraction(Typed(D(1), Complexes()),
        Typed(At(Qualified("Nat", "cast"), X(size)), Complexes()));
    private static Formula IsPOVM(Formula family) => At(Qualified("D5", "S3", "Quantum", "QuantumChannels",
        "ConcealmentKernelNecessityRefutation", "IsPOVM"), family);
    private static Formula Luders(Formula first, Formula second) => At(Qualified("D5", "S3", "Quantum",
        "Measurements", "CalibratedJointMeasurabilityOptimality", "luders"), first, second);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurement",
        "ConditionallyRandomUniformAttenuation", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Smul(Formula scalar, Formula matrix) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(matrix));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
