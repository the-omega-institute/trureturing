using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class EntropyProductionCoherenceDeletionIdentityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unitary evolution followed by coordinate-basis pinching produces entropy equal "
            + "to the deleted coherence, with nonnegative gains that telescope.",
        H("Entropy Production by Coherence Deletion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cfc-diagonal"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.cfc_diagonal"),
                H("Finite diagonal functional calculus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real function f and every finite real diagonal, actual complex matrix CFC "
                        + "applies f coordinatewise. The finite spectrum requires no global continuity assumption on "
                        + "f. The existing logarithm diagonal theorem consumes this extracted proof, and the Petz "
                        + "inverse-square-root coordinate argument also uses it. This is a shared organizing helper, "
                        + "not a separate mathematical gain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonal-star-algebra-hom"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity."
                        + "diagonalStarAlgHom"),
                H("The diagonal star-algebra homomorphism"),
                StatementSource.FromAuthor(DiagonalHomFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a finite decidable carrier, diagonalStarAlgHom sends each complex "
                        + "coordinate function to its diagonal matrix. Its underlying algebra "
                        + "homomorphism is Matrix.diagonalAlgHom, and the star law is "
                        + "coordinatewise complex conjugation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("basis-pinching-entropy"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity."
                        + "von_neumann_entropy_basisPinchingState"),
                H("Entropy of the coordinate pinching"),
                StatementSource.FromAuthor(PinchingEntropyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The entropy of coordinate-basis pinching is the negative sum of each "
                        + "real diagonal entry times its real logarithm."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("entropy-production-coherence-deletion-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity."
                        + "entropy_production_coherence_deletion_identity"),
                H("Entropy production equals deleted coherence"),
                StatementSource.FromAuthor(IdentityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let U be a unitary complex matrix on a finite decidable carrier. "
                            + "Starting from a sequence of density states, assume each next "
                            + "state is obtained by conjugating with U and then deleting the "
                            + "off-diagonal entries in the fixed coordinate basis.")),
                    Paragraph(Text(
                        "At every step, the entropy gain is exactly the quantum relative "
                            + "entropy from the evolved state to its pinched state, and this "
                            + "quantity is nonnegative. Summing these one-step identities "
                            + "gives the finite-horizon entropy balance."))),
                DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula DiagonalHomFormula()
    {
        Formula carrier = F.Id("n"), complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula coordinates = Seq(carrier, To, complex);
        Formula matrices = Call("Matrix", carrier, carrier, complex);
        Formula homType = Call("StarAlgHom", complex, coordinates, matrices);
        Formula hom = Seq(Operatorname, Grp(F.Id("diagonalStarAlgHom")));
        Formula a = F.Id("a"), i = F.Id("i"), j = F.Id("j");
        Formula entry = Seq(
            Forall, Sp, a, Colon, Sp, coordinates, Comma, Sp,
            Forall, Sp, i, Sp, j, Colon, Sp, carrier, Comma, Sp,
            Call("diagonalStarAlgHom", a, i, j), Sp, Eq, Sp,
            Call("ite", Seq(i, Eq, j), new Formula.Apply(a, [i]), D(0)));
        return Disp(Seq(
            Forall, Sp, Parenthesized(Seq(carrier, Colon, Sp,
                Operatorname, Grp(F.Id("Type")))), Sp,
            OpenBracket, Call("Fintype", carrier), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", carrier), CloseBracket, Comma, Sp,
            hom, Colon, Sp, homType, Comma, RowBreak, Grp(),
            Call("toAlgHom", hom), Sp, Eq, Sp,
            Call("diagonalAlgHom", complex), Sp, Land, Sp, Parenthesized(entry),
            Sp, Land, RowBreak, Grp(), Parenthesized(Seq(
                Forall, Sp, a, Colon, Sp, coordinates, Comma, Sp,
                Call("diagonalStarAlgHom", Call("star", a)), Sp, Eq, Sp,
                Call("star", Call("diagonalStarAlgHom", a))))));
    }

    private static Formula PinchingEntropyFormula()
    {
        Formula carrier = F.Id("n"), state = Rho, index = F.Id("i");
        Formula diagonal = Call("Re", Call("densityMatrix", state, index, index));
        Formula summand = Seq(diagonal, Sp, Call("log", diagonal));
        return Disp(Seq(
            Forall, Sp, Parenthesized(Seq(carrier, Colon, Sp,
                Operatorname, Grp(F.Id("Type")))), Sp,
            OpenBracket, Call("Fintype", carrier), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", carrier), CloseBracket, Comma, Sp,
            Forall, Sp, state, Colon, Sp, Call("DensityState", carrier), Comma, Sp,
            Call("vonNeumannEntropy", Call("basisPinchingState", state)), Sp, Eq, Sp,
            Minus, Parenthesized(Seq(
                new Formula.Subscript(Sum, Seq(index, Sp, Colon, Sp, carrier)), Sp, summand))));
    }

    private static Formula IdentityFormula()
    {
        Formula carrier = F.Id("n"), unitary = F.Id("U"), sequence = Rho;
        Formula step = F.Id("k"), horizon = F.Id("N");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula carrierType = Seq(Operatorname, Grp(F.Id("Type")));
        Formula matrixType = Call("Matrix", carrier, carrier, complex);
        Formula densityType = Call("DensityState", carrier);
        Formula sequenceType = Seq(natural, Sp, To, Sp, densityType);
        Formula unitaryProof = F.Id("hU");

        Formula StateAt(Formula index) => Sub(sequence, index);
        Formula EvolvedAt(Formula index) =>
            Call("unitaryConjugateState", unitary, unitaryProof, StateAt(index));
        Formula PinchedAt(Formula index) =>
            Call("basisPinchingState", EvolvedAt(index));
        Formula TaxAt(Formula index) =>
            Call("quantumRelativeEntropy", EvolvedAt(index), PinchedAt(index));
        Formula EntropyAt(Formula index) =>
            Call("vonNeumannEntropy", StateAt(index));

        Formula nextStep = Seq(step, Plus, D(1));
        Formula recurrence = Seq(
            Forall, Sp, step, Colon, Sp, natural, Comma, Sp,
            StateAt(nextStep), Sp, Eq, Sp, PinchedAt(step));
        Formula oneStep = Seq(
            Forall, Sp, step, Colon, Sp, natural, Comma, Sp,
            Parenthesized(Seq(
                EntropyAt(nextStep), Sp, Minus, Sp, EntropyAt(step), Sp, Eq, Sp,
                TaxAt(step),
                Sp, Land, Sp, D(0), Sp, Leq, Sp, TaxAt(step))));
        Formula totalTax = Seq(
            new Formula.Subscript(Sum,
                new Formula.Relation(step, FormulaRelationOperator.MemberOf, Call("range", horizon))),
            Sp, TaxAt(step));
        Formula telescope = Seq(
            Forall, Sp, horizon, Colon, Sp, natural, Comma, Sp,
            EntropyAt(horizon), Sp, Minus, Sp, EntropyAt(D(0)), Sp, Eq, Sp,
            totalTax);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Parenthesized(Seq(carrier, Colon, Sp, carrierType)), Sp,
            OpenBracket, Call("Fintype", carrier), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", carrier), CloseBracket, Comma, Sp,
            Forall, Sp,
            unitary, Colon, Sp, matrixType, Comma, Sp,
            Forall, Sp, Parenthesized(Seq(unitaryProof, Colon, Sp,
                unitary, Sp, InMacro, Sp, Call("unitaryGroup", carrier, complex))), Comma, Sp,
            Forall, Sp,
            sequence, Colon, Sp, sequenceType, Comma, RowBreak, Grp(),
            Parenthesized(recurrence), Sp, Rightarrow, RowBreak, Grp(),
            Parenthesized(oneStep), Sp, Land, RowBreak, Grp(),
            Parenthesized(telescope), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
