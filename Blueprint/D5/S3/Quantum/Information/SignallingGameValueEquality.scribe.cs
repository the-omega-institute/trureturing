using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class SignallingGameValueEqualityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/SignallingGameValueEquality";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/seshadrileditzkysiddhusmith2023signalling");

    private static Formula Named(string name)
    {
        var pieces = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (pieces.Count > 0)
                pieces.Add(Dot);
            pieces.Add(F.Id(part));
        }

        return Seq(Operatorname, Grp(Seq([.. pieces])));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);

    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula LocalCall(string name, params Formula[] arguments) =>
        At(Named(name), arguments);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));

    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Prop => F.Id("Prop");

    private static Formula M => F.Id("m");
    private static Formula N => F.Id("n");
    private static Formula Da => F.Id("da");
    private static Formula Db => F.Id("db");
    private static Formula P => F.Id("p");
    private static Formula Fa => F.Id("fa");
    private static Formula Fb => F.Id("fb");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula U => F.Id("u");
    private static Formula V => F.Id("v");
    private static Formula Rho => F.Id("rho");
    private static Formula Value => F.Id("v");

    private static Formula Fin(Formula size) => Call("Fin", size);

    private static Formula ProbabilityType =>
        Arrow(Fin(N), Arrow(Fin(M), Arrow(Fin(M), Arrow(Fin(N), Real))));

    private static Formula MatrixType(Formula rows, Formula columns, Formula field) =>
        Call("Matrix", rows, columns, field);

    private static Formula PairType(Formula left, Formula right) =>
        Parenthesized(Seq(left, Times, Sp, right));

    private static Formula TensorIndex =>
        PairType(Fin(Da), Fin(Db));

    private static Formula BipartiteMatrix =>
        MatrixType(TensorIndex, TensorIndex, Complex);

    private static Formula AliceMeasurement =>
        Arrow(Fin(M), Arrow(Fin(N), MatrixType(Fin(Da), Fin(Da), Complex)));

    private static Formula BobMeasurement =>
        Arrow(Fin(N), Arrow(Fin(M), MatrixType(Fin(Db), Fin(Db), Complex)));

    private static Formula OneReal => Typed(D(1), Real);
    private static Formula ZeroReal => Typed(D(0), Real);
    private static Formula CastReal(Formula value) => Typed(value, Real);

    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, Colon, Sp, type)), Sp, Parenthesized(body));

    private static Formula MaxNat(Formula left, Formula right) =>
        Call("max", CastReal(left), CastReal(right));

    private static Formula ValueAt(Formula function, params Formula[] arguments) =>
        At(function, arguments);

    private static Formula SetBuilder(Formula variable, Formula type, Formula body) =>
        Seq(OpenBrace, Typed(variable, type), Sp, Mid, Sp, body, CloseBrace);

    private static Formula IsNoSignallingBody()
    {
        Formula nonnegative = All(A, Fin(N), All(B, Fin(M), All(X, Fin(M), All(Y, Fin(N),
            Le(ZeroReal, ValueAt(P, A, B, X, Y))))));
        Formula normalized = All(X, Fin(M), All(Y, Fin(N),
            Eq(SumOver(A, Fin(N), SumOver(B, Fin(M), ValueAt(P, A, B, X, Y))), OneReal)));
        Formula aliceMarginal = All(A, Fin(N), All(X, Fin(M), All(Y, Fin(N), All(F.Id("z"), Fin(N),
            Eq(SumOver(B, Fin(M), ValueAt(P, A, B, X, Y)),
                SumOver(B, Fin(M), ValueAt(P, A, B, X, F.Id("z"))))))));
        Formula bobMarginal = All(B, Fin(M), All(X, Fin(M), All(F.Id("z"), Fin(M), All(Y, Fin(N),
            Eq(SumOver(A, Fin(N), ValueAt(P, A, B, X, Y)),
                SumOver(A, Fin(N), ValueAt(P, A, B, F.Id("z"), Y)))))));
        return And(nonnegative, And(normalized, And(aliceMarginal, bobMarginal)));
    }

    private static Formula IsNoSignallingFormula() =>
        All(M, Nat, All(N, Nat, All(P, ProbabilityType,
            Iff(LocalCall("IsNoSignalling", P), IsNoSignallingBody()))));

    private static Formula WinProbBody() =>
        new Formula.Binary(
            new Formula.Fraction(D(1), Parenthesized(new Formula.Binary(
                CastReal(M), FormulaBinaryOperator.Multiply, CastReal(N)))),
            FormulaBinaryOperator.Multiply,
            SumOver(X, Fin(M), SumOver(Y, Fin(N), ValueAt(P, Y, X, X, Y))));

    private static Formula WinProbFormula() =>
        All(M, Nat, All(N, Nat, All(P, ProbabilityType,
            Eq(Typed(LocalCall("winProb", P), Real), WinProbBody()))));

    private static Formula DeterministicBoxFormula()
    {
        Formula faType = Arrow(Fin(M), Fin(N));
        Formula fbType = Arrow(Fin(N), Fin(M));
        Formula body = new Formula.Binary(
            Call("labelKernel", Fa, X, A),
            FormulaBinaryOperator.Multiply,
            Call("labelKernel", Fb, Y, B));
        return All(M, Nat, All(N, Nat, All(Fa, faType, All(Fb, fbType,
            All(A, Fin(N), All(B, Fin(M), All(X, Fin(M), All(Y, Fin(N),
                Eq(Typed(LocalCall("deterministicBox", Fa, Fb, A, B, X, Y), Real), body)))))))));
    }

    private static Formula ClassicalValuesFormula()
    {
        Formula witnesses = Some(Fa, Arrow(Fin(M), Fin(N)),
            Some(Fb, Arrow(Fin(N), Fin(M)),
                Eq(LocalCall("winProb", LocalCall("deterministicBox", Fa, Fb)), Value)));
        return All(M, Nat, All(N, Nat,
            Eq(LocalCall("classicalValues", M, N), SetBuilder(Value, Real, witnesses))));
    }

    private static Formula IsQuantumStrategyBody()
    {
        Formula density = Call("IsDensity", Rho);
        Formula alice = All(X, Fin(M), Call("IsPOVM", At(A, X)));
        Formula bob = All(Y, Fin(N), Call("IsPOVM", At(B, Y)));
        return And(density, And(alice, bob));
    }

    private static Formula IsQuantumStrategyFormula() =>
        All(M, Nat, All(N, Nat, All(Da, Nat, All(Db, Nat,
            All(Rho, BipartiteMatrix, All(A, AliceMeasurement, All(B, BobMeasurement,
                Iff(LocalCall("IsQuantumStrategy", Rho, A, B), IsQuantumStrategyBody()))))))));

    private static Formula QuantumBoxFormula()
    {
        Formula x1 = F.Id("x1");
        Formula x2 = F.Id("x2");
        Formula tensorLambda = Seq(
            F.Id("fun"), Sp, x1, Sp, x2, Sp, Mapsto, Sp,
            new Formula.Binary(x1, FormulaBinaryOperator.Multiply, x2));
        Formula kron = At(Named("Matrix.kroneckerMap"), tensorLambda, At(A, X, U), At(B, Y, V));
        Formula born = Call("bornProbability", Rho, kron);
        Formula realPart = Call("Complex.re", born);
        return All(M, Nat, All(N, Nat, All(Da, Nat, All(Db, Nat,
            All(Rho, BipartiteMatrix, All(A, AliceMeasurement, All(B, BobMeasurement,
                All(U, Fin(N), All(V, Fin(M), All(X, Fin(M), All(Y, Fin(N),
                    Eq(Typed(LocalCall("quantumBox", Rho, A, B, U, V, X, Y), Real), realPart))))))))))));
    }

    private static Formula QuantumValuesFormula()
    {
        Formula witnesses = Some(Da, Nat, Some(Db, Nat, Some(Rho, BipartiteMatrix,
            Some(A, AliceMeasurement, Some(B, BobMeasurement,
                And(Call("IsQuantumStrategy", Rho, A, B),
                    Eq(LocalCall("winProb", LocalCall("quantumBox", Rho, A, B)), Value)))))));
        return All(M, Nat, All(N, Nat,
            Eq(LocalCall("quantumValues", M, N), SetBuilder(Value, Real, witnesses))));
    }

    private static Formula NoSignallingValuesFormula()
    {
        Formula witnesses = Some(P, ProbabilityType,
            And(Call("IsNoSignalling", P),
                Eq(LocalCall("winProb", P), Value)));
        return All(M, Nat, All(N, Nat,
            Eq(LocalCall("noSignallingValues", M, N), SetBuilder(Value, Real, witnesses))));
    }

    private static Formula ClaimBody()
    {
        Formula target = new Formula.Binary(D(1), FormulaBinaryOperator.Multiply, D(1));
        target = new Formula.Fraction(D(1), MaxNat(M, N));
        Formula classical = Call("IsGreatest", LocalCall("classicalValues", M, N), target);
        Formula quantum = Call("IsGreatest", LocalCall("quantumValues", M, N), target);
        Formula noSignalling = Call("IsGreatest", LocalCall("noSignallingValues", M, N), target);
        return All(M, Nat, All(N, Nat,
            Imp(Le(D(1), M), Imp(Le(D(1), N),
                And(noSignalling, And(quantum, classical))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signalling game has classical, quantum and no-signalling value 1/max(m,n).",
        H("Signalling-game value equality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("is-no-signalling"),
                DeclarationHandle.Create(Module + ".IsNoSignalling"),
                H("No-signalling conditional probabilities"),
                StatementSource.FromAuthor(Disp(IsNoSignallingFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For questions x and y and answers a and b, IsNoSignalling requires nonnegative probabilities, normalization for each question pair, and independence of Alice's marginal from Bob's question and of Bob's marginal from Alice's question."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("win-probability"),
                DeclarationHandle.Create(Module + ".winProb"),
                H("Uniform winning probability"),
                StatementSource.FromAuthor(Disp(WinProbFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The questions are uniform on Fin m and Fin n. The winning event is that the first answer equals the second question and the second answer equals the first question, so winProb averages p y x x y over all question pairs and divides by the product of the two cardinalities."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("deterministic-box"),
                DeclarationHandle.Create(Module + ".deterministicBox"),
                H("A deterministic local box"),
                StatementSource.FromAuthor(Disp(DeterministicBoxFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Given local response functions fa from Fin m to Fin n and fb from Fin n to Fin m, deterministicBox is the product of the two indicator kernels for the selected answers and questions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("classical-values"),
                DeclarationHandle.Create(Module + ".classicalValues"),
                H("Classical deterministic values"),
                StatementSource.FromAuthor(Disp(ClassicalValuesFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "classicalValues m n is the set of real winning probabilities obtained from pairs of deterministic local response functions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-quantum-strategy"),
                DeclarationHandle.Create(Module + ".IsQuantumStrategy"),
                H("Finite-dimensional quantum strategies"),
                StatementSource.FromAuthor(Disp(IsQuantumStrategyFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A quantum strategy consists of a bipartite complex density matrix rho and a POVM for every question on each side. Alice's measurements act on the first local dimension and Bob's on the second."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quantum-box"),
                DeclarationHandle.Create(Module + ".quantumBox"),
                H("The Born-rule correlation box"),
                StatementSource.FromAuthor(Disp(QuantumBoxFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "quantumBox is the real part of Born's probability for the tensor product of Alice's effect for answer u and Bob's effect for answer v, evaluated at questions x and y."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quantum-values"),
                DeclarationHandle.Create(Module + ".quantumValues"),
                H("Quantum strategy values"),
                StatementSource.FromAuthor(Disp(QuantumValuesFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "quantumValues m n contains exactly the winning probabilities of all finite local dimensions, bipartite density matrices, and local POVM families satisfying IsQuantumStrategy."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("no-signalling-values"),
                DeclarationHandle.Create(Module + ".noSignallingValues"),
                H("No-signalling strategy values"),
                StatementSource.FromAuthor(Disp(NoSignallingValuesFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "noSignallingValues m n contains the winning probabilities of all normalized nonnegative boxes satisfying IsNoSignalling."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The common sharp value"),
                StatementSource.FromAuthor(Disp(Eq(Typed(Named("claim"), Prop), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every pair of nonempty finite question sets, the greatest no-signalling, quantum, and classical deterministic winning probabilities are all 1/max(m,n)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The signalling-game equality is proved"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Choose response functions fa and fb that reduce indices modulo their respective target dimensions: fa sends x to x mod n and fb sends y to y mod m. If m is at most n, fb composed with fa is the identity on Fin m; if n is at most m, fa composed with fb is the identity on Fin n. In either case the deterministic box wins on exactly the smaller question set, so its uniform winning probability is 1/max(m,n).")),
                    Paragraph(Text(
                        "Realize this deterministic box as a one-dimensional quantum strategy. Take the one-by-one density matrix and diagonal one-by-one POVM effects whose entries are the local indicator kernels. The POVMs sum to the identity, and direct evaluation of Born's rule gives quantumBox equal to deterministicBox.")),
                    Paragraph(Text(
                        "Every quantum strategy induces a no-signalling box. Summing Bob's POVM over his answers replaces it by the identity on Bob's space, and summing Alice's POVM does the same on Alice's space. Positivity follows from positivity of the state and the two effects; normalization follows from trace one. The resulting marginal sums are independent of the other question.")),
                    Paragraph(Text(
                        "For any no-signalling box, the winning sum is bounded by m using Alice's marginal and by n using Bob's marginal: each winning term is bounded by the corresponding marginal term, and the relevant normalized marginal sums equal one. Splitting into m at most n or n at most m turns these bounds into winProb at most 1/max(m,n).")),
                    Paragraph(Text(
                        "The deterministic construction supplies an element attaining the bound in every class. The no-signalling upper bound applies directly to noSignallingValues and, through the quantum-to-no-signalling construction, to quantumValues. For a classical value, embed each deterministic box into a one-dimensional quantum strategy and apply the same bound. The three IsGreatest statements follow."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("seshadri-leditzky-siddhu-smith-2023-signalling-game-values"),
                    ResolutionKind.Proved)))));
}
