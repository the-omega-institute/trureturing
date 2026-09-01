using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class LocalEulerFrameHistoryNonreconstructionDocument
    : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Observer/AgencyHolonomy/LocalEulerFrameHistoryNonreconstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite local Euler shadow does not determine frame history or "
            + "cross-prime transitions.",
        H("Local Euler Frame-History Non-Reconstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("local-euler-frame-history-non-reconstruction"),
            DeclarationHandle.Create(
                Handle + "local_euler_determinants_do_not_reconstruct_frame_history"),
            H("Local determinants cannot clone frame history"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The local operator at each prime is the canonical diagonal "
                        + "two-branch operator with eigenvalues one and chi at that prime. "
                        + "Its framed Euler determinant is the finite spectral shadow "
                        + "retained by the scalar observation.")),
                Paragraph(Text(
                    "The frozen local-transition owner supplies two frame histories whose "
                        + "determinants both equal the same explicit Euler polynomial at "
                        + "every prime and scalar. Their histories are distinct and their "
                        + "transitions from prime two to prime three differ.")),
                Paragraph(Text(
                    "No decoder of the complete local determinant family can return both "
                        + "histories correctly. This is stronger input than two global "
                        + "scalar functions, so those functions cannot clone the framed "
                        + "observer or its formation history."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complex = Call("Complex");
        Formula finTwo = Call("Fin", D(2));
        Formula matrix = Call("Matrix", finTwo, finTwo, complex);
        Formula generalLinear = Call("GL", finTwo, complex);
        Formula primes = Seq(F.Id("Nat"), Dot, F.Id("Primes"));
        Formula chi = F.Id("chi");
        Formula p2 = Seq(F.Id("p"), Underscore, D(2));
        Formula p3 = Seq(F.Id("p"), Underscore, D(3));
        Formula localOperator = F.Id("localOperator");
        Formula firstFrame = F.Id("firstFrame");
        Formula secondFrame = F.Id("secondFrame");
        Formula p = F.Id("p");
        Formula x = F.Id("x");
        Formula branch = F.Id("branch");
        Formula reconstruct = F.Id("R");
        Formula frameFamily = Arrow(primes, generalLinear);
        Formula determinantFamily = Arrow(primes, Arrow(complex, complex));

        Formula localDefinition = Lambda(
            p,
            primes,
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
            Call("inverse", FrameAt(frame, p3)),
            FrameAt(frame, p2));
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
            [Bound("p", primes), Bound("x", complex)],
            Equal(EulerDeterminant(frame), expectedDeterminant));
        Formula Shadow(Formula frame) => LambdaPair(
            p,
            x,
            EulerDeterminant(frame));

        Formula decoderRecoversBoth = Exists(
            [Bound("R", Arrow(determinantFamily, frameFamily))],
            And(
                Equal(Apply(reconstruct, Shadow(firstFrame)), firstFrame),
                Equal(Apply(reconstruct, Shadow(secondFrame)), secondFrame)));

        Formula conclusion = Exists(
            [
                Bound("firstFrame", frameFamily),
                Bound("secondFrame", frameFamily),
            ],
            All(
                SameLocalDeterminants(firstFrame),
                SameLocalDeterminants(secondFrame),
                NotEqual(firstFrame, secondFrame),
                NotEqual(Transition(firstFrame), Transition(secondFrame)),
                new Formula.Not(decoderRecoversBoth)));

        return Disp(ForAll(
            [Bound("chi", Arrow(primes, complex))],
            Seq(
                Let(p2, primes, Call("prime", D(2))),
                Let(p3, primes, Call("prime", D(3))),
                Let(
                    localOperator,
                    Arrow(primes, matrix),
                    localDefinition),
                conclusion)));
    }

    private static Formula Let(Formula name, Formula type, Formula value) =>
        Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            name, Colon, Sp, type, Sp, Eq, Sp, value, Comma, Sp);

    private static Formula Lambda(Formula name, Formula type, Formula body) =>
        Seq(Open, name, Colon, Sp, type, Sp, Mapsto, Sp, body, Close);

    private static Formula LambdaPair(
        Formula first,
        Formula second,
        Formula body) =>
        Seq(
            Open, Open, first, Comma, Sp, second, Close,
            Sp, Mapsto, Sp, body, Close);

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
