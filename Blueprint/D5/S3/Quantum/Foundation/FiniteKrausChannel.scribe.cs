using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FiniteKrausChannelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Kraus realizations in the canonical completely positive channel interface.",
        H("Finite Kraus Quantum Channels"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-kraus-canonical-channel"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Foundation/FiniteKrausChannel.finite_kraus_quantum_channel"),
            H("Kraus completeness gives a canonical quantum channel"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A, B and R are arbitrary finite coordinate types, including empty types. "
                    + "K(r) is a complex matrix from A to B. The sole matrix hypothesis is "
                    + "the displayed completeness identity.")),
                Paragraph(Text(
                    "QuantumChannel is the canonical FiniteStateChannel bundle: a Mathlib "
                    + "CompletelyPositiveMap on CStarMatrix, positive at every finite amplification, "
                    + "together with trace preservation for every matrix. The functions toCstar "
                    + "and fromCstar are CStarMatrix.ofMatrix and its inverse. Adjoint means "
                    + "conjugate transpose. The displayed action holds for every input matrix.")),
                Paragraph(Text(
                    "The private proof closure retains Alex Meiburg's Physlib Kraus complete "
                    + "positivity and trace preservation proofs from revision "
                    + "6a09b2d1761a0d4430083045a247eb121d8da260, under the full Apache 2.0 "
                    + "license retained in the Lean source. A star algebra coordinate equivalence "
                    + "transports its Kronecker amplification to canonical CStarMatrix amplification. "
                    + "The retained closure retires when equivalent declarations enter pinned Mathlib. "
                    + "The concrete shifted-record realization consumes this bridge."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Conj(Formula a) => Seq(a, Caret, Grp(Star));
    private static Formula All(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B"), rtype = F.Id("R");
        Formula r = F.Id("r"), k = F.Id("K"), channel = F.Id("C"), rho = F.Id("rho");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula ka = new Formula.Apply(k, [r]);
        Formula input = Call("Matrix", a, a, complex);
        Formula SumOver(Formula body) => Seq(Sum, Underscore,
            Grp(r, Sp, InMacro, Sp, rtype), Sp, body);
        Formula completeness = Eqn(SumOver(Mul(Conj(ka), ka)), Num(1));
        Formula action = All([Bound("rho", input)], Eqn(
            Call("fromCstar", Call("apply", channel, Call("toCstar", rho))),
            SumOver(Mul(Mul(ka, rho), Conj(ka)))));
        Formula result = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("C", Call("QuantumChannel", a, b))], action);
        return Disp(All(
            [Bound("A", F.Id("FiniteType")), Bound("B", F.Id("FiniteType")),
                Bound("R", F.Id("FiniteType")),
                Bound("K", new Formula.TypeArrow(rtype, Call("Matrix", b, a, complex)))],
            new Formula.Logic(completeness, FormulaLogicOperator.Implies, result)));
    }
}
