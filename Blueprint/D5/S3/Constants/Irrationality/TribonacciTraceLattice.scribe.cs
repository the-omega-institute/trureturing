using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Irrationality;

internal sealed class TribonacciTraceLatticeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var naturals = Id("N");
        var integers = Id("Z");
        var v1 = Id("v1");
        var v2 = Id("v2");
        var z = Id("z");

        Formula And(Formula left, Formula right) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right);

        var nonintegralWitness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("v1"), naturals),
                new Formula.BoundVariable(FormulaIdentifier.Create("v2"), naturals),
            ],
            new Formula.Not(new Formula.BindMany(
                FormulaQuantifier.Exists,
                [new Formula.BoundVariable(FormulaIdentifier.Create("z"), integers)],
                Equal(Call("tribonacciDeficit", v1, v2), z))));

        var fibonacciIntegrality = Call("HasIntegralDeficit", Id("fibonacci"));
        var tribonacciIntegrality = Call("HasIntegralDeficit", Id("tribonacci"));
        var privilege = NotEqual(fibonacciIntegrality, tribonacciIntegrality);
        var nonreplaceability = new Formula.Not(tribonacciIntegrality);

        var statement = And(nonintegralWitness, And(privilege, nonreplaceability));

        const string declarationPrefix =
            "D5/S3/Constants/Irrationality/TribonacciTraceLattice.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The Tribonacci deficit is nonintegral somewhere, and integrality distinguishes the Fibonacci encoding.",
            H("Tribonacci Deficit Integrality Contrast"),
            Blocks(
                Paragraph(Text(
                    "There exist natural inputs v1 and v2 for which the Binet-main-term "
                        + "Tribonacci deficit has no integer representative. This is an "
                        + "unrestricted existential statement: the finite scan used to find "
                        + "the witness is not a hypothesis in the Lean declaration.")),
                Paragraph(Text(
                    "For the concrete two-element comparison carrier, the Fibonacci and "
                        + "Tribonacci HasIntegralDeficit propositions are unequal. Moreover, "
                        + "the Tribonacci proposition is false, so the Fibonacci encoding "
                        + "cannot be replaced by the Tribonacci encoding.")),
                Paragraph(Text(
                    "What this does not claim: it does not identify an input domain behind the "
                        + "reported output bound or 44.4 percent; it does not identify a "
                        + "nonintegral topological spectrum with an additive trace lattice; and "
                        + "it does not claim a quadratic embedding-exhaustion theorem, a cubic "
                        + "one-real/two-complex signature, or an Algebra.trace obstruction. "
                        + "Those clauses lack the required source-specific carriers.")),
                Paragraph(Text(
                    "The previous thirteen-leaf finite-window result remains available as "
                        + "tribonacci_trace_lattice_window_certificate. It preserves the exact "
                        + "bound, count, rounding, code image, congruence, and supporting root "
                        + "facts without presenting them as source clauses of this theorem.")),
                Describe.Lean(
                    DescribeId.Create("pzg-remark-six-twenty-seven-tribonacci-trace-lattice"),
                    DeclarationHandle.Create(
                        declarationPrefix + "pzg_remark_6_27_tribonacci_trace_lattice"),
                    H("PZG Remark 6.27: nonintegrality and two-faced privilege"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The public type has two conjunction nodes and three independently "
                            + "projectable leaves: the existential CAS-A2 witness, the CAS-A10 "
                            + "privilege relation, and the CAS-A11 nonreplaceability negation."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S3/Constants/Irrationality/TribonacciDeficitScanCertificate")),
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S3/Constants/Irrationality/CubicConjugateTrace")),
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S3/Constants/Irrationality/TwoFacedPrivilege")),
            ]));
    }
}
