using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class LocalEulerTransitionNonreconstructionDocument
    : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Observer/AgencyHolonomy/LocalEulerTransitionNonreconstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Euler determinants do not determine cross-address frame transitions.",
        H("Local Euler Transition Non-Reconstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("local-euler-transition-non-reconstruction"),
            DeclarationHandle.Create(
                Handle + "local_euler_determinants_do_not_determine_transition"),
            H("Local determinants forget frame transitions"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The local operator at each of two addresses is the diagonal "
                        + "two-branch operator with eigenvalues one and chi at that "
                        + "address.")),
                Paragraph(Text(
                    "Two general-linear frame families produce the same local Euler "
                        + "determinant for every address and scalar parameter, while "
                        + "their inverse-frame transition products are unequal."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complex = Call("Complex");
        Formula finTwo = Call("Fin", D(2));
        Formula matrix = Call("Matrix", finTwo, finTwo, complex);
        Formula generalLinear = Call("GL", finTwo, complex);
        Formula chi = F.Id("chi");
        Formula localOperator = F.Id("localOperator");
        Formula firstFrame = F.Id("firstFrame");
        Formula secondFrame = F.Id("secondFrame");
        Formula p = F.Id("p");
        Formula x = F.Id("x");
        Formula branch = F.Id("branch");

        Formula localDefinition = Lambda(
            p,
            finTwo,
            Call(
                "diagonal",
                Lambda(
                    branch,
                    finTwo,
                    Call(
                        "ite",
                        Equal(branch, D(0)),
                        D(1),
                        Apply(chi, p)))));
        Formula FrameAt(Formula frame, Formula address) => Apply(frame, address);
        Formula Transition(Formula frame) => Multiply(
            Call("inverse", FrameAt(frame, D(1))),
            FrameAt(frame, D(0)));
        Formula FramedOperator(Formula frame) => Multiply(
            Multiply(FrameAt(frame, p), Apply(localOperator, p)),
            Call("inverse", FrameAt(frame, p)));
        Formula EulerDeterminant(Formula frame) => Call(
            "det",
            Subtract(
                Call("identityMatrix", finTwo, complex),
                Call("smul", x, FramedOperator(frame))));
        Formula expectedDeterminant = Multiply(
            Subtract(D(1), x),
            Subtract(D(1), Multiply(x, Apply(chi, p))));
        Formula SameLocalDeterminants(Formula frame) => ForAll(
            [Bound("p", finTwo), Bound("x", complex)],
            Equal(EulerDeterminant(frame), expectedDeterminant));

        Formula conclusion = Exists(
            [
                Bound("firstFrame", Arrow(finTwo, generalLinear)),
                Bound("secondFrame", Arrow(finTwo, generalLinear)),
            ],
            All(
                SameLocalDeterminants(firstFrame),
                SameLocalDeterminants(secondFrame),
                NotEqual(Transition(firstFrame), Transition(secondFrame))));

        return Disp(ForAll(
            [Bound("chi", Arrow(finTwo, complex))],
            Seq(
                Let(
                    localOperator,
                    Arrow(finTwo, matrix),
                    localDefinition),
                conclusion)));
    }

    private static Formula Let(Formula name, Formula type, Formula value) =>
        Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            name, Colon, Sp, type, Sp, Eq, Sp, value, Comma, Sp);

    private static Formula Lambda(Formula name, Formula type, Formula body) =>
        Seq(Open, name, Colon, Sp, type, Sp, Mapsto, Sp, body, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    private static Formula ForAll(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
