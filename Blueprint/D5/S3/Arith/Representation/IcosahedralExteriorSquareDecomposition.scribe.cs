using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Representation;

internal sealed class IcosahedralExteriorSquareDecompositionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Arith/Representation/IcosahedralExteriorSquareDecomposition."
            + "exterior_square_decomposes_into_icosahedral_pair";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real A5 exterior square splits into its two Galois-conjugate "
            + "icosahedral summands.",
        H("Icosahedral Exterior-Square Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("icosahedral-exterior-square-decomposition"),
                DeclarationHandle.Create(Declaration),
                H("The second exterior power is the complete icosahedral pair"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here A5 is the concrete alternatingGroup on Fin 5. The standard "
                            + "state V4 is the real subspace of five coordinates with zero "
                            + "sum, acted on by even coordinate permutations, and the "
                            + "second-order representation is the induced action on the "
                            + "genuine exterior power Lambda^2 V4.")),
                    Paragraph(Text(
                        "The parameters rho3 and rho3Prime are representations on two real "
                            + "three-dimensional carriers. Their two irreducibility premises "
                            + "and the GoldenGaloisCharacterPair premise carry exactly the "
                            + "source identification of V3 and V3Prime as distinct golden "
                            + "Galois-conjugate icosahedral irreducibles. The final premise is "
                            + "the character-sum equality calculated in the source proof.")),
                    Paragraph(Text(
                        "The first conclusion is a genuine A5-equivariant linear equivalence "
                            + "from Lambda^2 V4 to the product representation rho3.prod "
                            + "rho3Prime. The second conclusion separately records the induced "
                            + "real linear equivalence from the six-dimensional product carrier "
                            + "to the complete second-order observation space; neither leaf is "
                            + "merely a character or dimension equality.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies the character inner-product formula, Schur "
                            + "injectivity, and Maschke splitting. Distinctness kills both cross "
                            + "intertwiner spaces; nonzero embeddings of the two irreducibles "
                            + "then have disjoint images, and character equality at the identity "
                            + "shows that their copairing exhausts the exterior square."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = F.Id("Real");
        Formula a5 = F.Id("A5");
        Formula realThree = Call("Pi", F.Id("Fin3"), real);
        Formula representationType = Call("Representation", real, a5, realThree);
        Formula rho3 = F.Id("rho3");
        Formula rho3Prime = F.Id("rho3Prime");
        Formula secondOrder = F.Id("secondOrderRepresentation");
        Formula completion = F.Id("IcosahedralCompletionSpace");
        Formula observation = F.Id("SecondOrderObservationSpace");

        Formula hypotheses = new Formula.Logic(
            Call("IsIrreducible", rho3),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Call("IsIrreducible", rho3Prime),
                FormulaLogicOperator.And,
                new Formula.Logic(
                    Call("GoldenGaloisCharacterPair", rho3, rho3Prime),
                    FormulaLogicOperator.And,
                    Equal(
                        Call("character", secondOrder),
                        Add(Call("character", rho3), Call("character", rho3Prime))))));

        Formula conclusions = new Formula.Logic(
            Call(
                "Nonempty",
                Call(
                    "RepresentationEquiv",
                    secondOrder,
                    Call("prod", rho3, rho3Prime))),
            FormulaLogicOperator.And,
            Call(
                "Nonempty",
                Call("RealLinearEquiv", completion, observation)));

        Formula statement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("rho3"), representationType),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("rho3Prime"), representationType),
            ],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, conclusions));

        return Disp(statement);
    }
}
