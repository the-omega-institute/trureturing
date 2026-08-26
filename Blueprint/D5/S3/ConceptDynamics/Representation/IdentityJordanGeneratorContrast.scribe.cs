using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Representation;

internal sealed class IdentityJordanGeneratorContrastDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrast.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The identity and a rational Jordan action are nonisomorphic but have the same "
            + "semisimple characteristic data.",
        H("Identity and Jordan Generator Contrast"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("identity-generator-minimal-polynomial"),
                DeclarationHandle.Create(DeclarationPrefix + "rho_zero_minpoly"),
                H("The identity generator has a linear minimal polynomial"),
                StatementSource.FromAuthor(RhoZeroMinpolyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use the free cyclic group Multiplicative integers and rational "
                            + "two-by-two matrices. The first action sends every group element "
                            + "to the identity matrix, so its generator has minimal polynomial "
                            + "X minus one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("jordan-generator-minimal-polynomial"),
                DeclarationHandle.Create(DeclarationPrefix + "rho_unipotent_minpoly"),
                H("The Jordan generator has a quadratic minimal polynomial"),
                StatementSource.FromAuthor(RhoUnipotentMinpolyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Jordan generator is not a scalar matrix, so the minimal polynomial "
                            + "has degree at least two. Cayley-Hamilton makes it divide the "
                            + "quadratic characteristic polynomial, forcing equality with the "
                            + "square of X minus one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cyclic-representations-not-isomorphic"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "representations_not_isomorphic"),
                H("The cyclic representations are not isomorphic"),
                StatementSource.FromAuthor(NotIsomorphicFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a free cyclic representation, an isomorphism conjugates the "
                            + "generator matrices. Unit conjugation preserves the minimal "
                            + "polynomial, while the two computed polynomials have different "
                            + "degrees. Hence no conjugating unit exists."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-semisimplification-charpoly"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "same_semisimplification_charpoly"),
                H("Both actions have the same semisimple characteristic data"),
                StatementSource.FromAuthor(CommonCharpolyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Pinned Mathlib has no semisimplification interface. This module records "
                            + "the source contrast by proving that both characteristic "
                            + "polynomials are the square of X minus one. Over the rationals in "
                            + "dimension two, that split polynomial records two trivial "
                            + "composition factors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conjugacy-hypothesis-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "conjugacy_hypothesis_is_necessary"),
                H("Conjugacy is necessary for minimal-polynomial invariance"),
                StatementSource.FromAuthor(ConjugacyNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two concrete generator matrices supply the required hypothesis "
                            + "counterexample. They are not conjugate, and their minimal "
                            + "polynomials have degrees one and two. Thus the conjugacy premise "
                            + "in the private invariance lemma cannot be removed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("generator-power-degenerate-audit"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "generator_power_degenerate_audit"),
                H("Jordan powers grow linearly and degenerate at zero"),
                StatementSource.FromAuthor(PowerAuditFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The upper-right entry of the nth positive generator power is n. At "
                            + "n equal to zero this entry vanishes, and the whole action is the "
                            + "identity action."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("trivial-action-degenerate-audit"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "trivial_action_degenerate_audit"),
                H("The identity action is self-conjugate and zero is not invertible"),
                StatementSource.FromAuthor(TrivialAuditFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first representation is self-conjugate and explicitly constant at "
                            + "the identity. The zero two-by-two matrix has zero determinant and "
                            + "is not a unit, so it cannot be a cyclic group generator image."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("low-dimension-degenerate-audit"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "low_dimension_degenerate_audit"),
                H("Empty and one-dimensional carriers collapse the contrast"),
                StatementSource.FromAuthor(LowDimensionAuditFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the empty matrix carrier, zero and identity are the same empty "
                            + "function. In dimension one there is no off-diagonal coordinate, "
                            + "so the identity and would-be Jordan generators coincide. The "
                            + "two-dimensional carrier is therefore essential."))),
                DescribeRole.Theorem))));

    private static Formula RhoZeroMinpolyFormula()
    {
        Formula generatorAction = Call("act", F.Id("rhoZero"), F.Id("g"));
        return Disp(Equal(
            Call("minpolyQ", generatorAction),
            Seq(F.Id("X"), Sp, Minus, Sp, D(1))));
    }

    private static Formula RhoUnipotentMinpolyFormula()
    {
        Formula generatorAction = Call("act", F.Id("rhoUnipotent"), F.Id("g"));
        Formula linearFactor = Seq(F.Id("X"), Sp, Minus, Sp, D(1));
        return Disp(Equal(
            Call("minpolyQ", generatorAction),
            Seq(Open, linearFactor, Close, Caret, D(2))));
    }

    private static Formula NotIsomorphicFormula() =>
        Disp(Seq(
            Neg, Sp,
            Call(
                "IsConj",
                Call("act", F.Id("rhoZero"), F.Id("g")),
                Call("act", F.Id("rhoUnipotent"), F.Id("g")))));

    private static Formula CommonCharpolyFormula()
    {
        Formula linearFactor = Seq(F.Id("X"), Sp, Minus, Sp, D(1));
        Formula square = Seq(Open, linearFactor, Close, Caret, D(2));
        Formula zeroCharpoly = Equal(
            Call("charpoly", Call("act", F.Id("rhoZero"), F.Id("g"))),
            square);
        Formula unipotentCharpoly = Equal(
            Call("charpoly", Call("act", F.Id("rhoUnipotent"), F.Id("g"))),
            square);
        return Disp(Seq(zeroCharpoly, Sp, Land, Sp, unipotentCharpoly));
    }

    private static Formula ConjugacyNecessityFormula()
    {
        Formula zeroAction = Call("act", F.Id("rhoZero"), F.Id("g"));
        Formula unipotentAction = Call("act", F.Id("rhoUnipotent"), F.Id("g"));
        Formula notConjugate = Seq(
            Neg, Sp, Call("IsConj", zeroAction, unipotentAction));
        Formula minpolysDiffer = NotEqual(
            Call("minpolyQ", zeroAction),
            Call("minpolyQ", unipotentAction));
        return Disp(Seq(notConjugate, Sp, Land, Sp, minpolysDiffer));
    }

    private static Formula PowerAuditFormula()
    {
        Formula n = F.Id("n");
        Formula generatorPower = Seq(F.Id("g"), Caret, n);
        Formula action = Call("act", F.Id("rhoUnipotent"), generatorPower);
        Formula matrix = Call("matrix2", D(1), n, D(0), D(1));
        Formula formula = Seq(
            Forall, Sp, n, Comma, Sp,
            Equal(action, matrix));
        Formula zeroPower = Seq(F.Id("g"), Caret, D(0));
        Formula zeroCase = Equal(
            Call("act", F.Id("rhoUnipotent"), zeroPower),
            Call("act", F.Id("rhoZero"), F.Id("g")));
        return Disp(Seq(formula, Sp, Land, Sp, zeroCase));
    }

    private static Formula TrivialAuditFormula()
    {
        Formula z = F.Id("z");
        Formula zeroAction = Call("act", F.Id("rhoZero"), F.Id("g"));
        Formula selfConjugate = Call("IsConj", zeroAction, zeroAction);
        Formula constantIdentity = Seq(
            Forall, Sp, z, Comma, Sp,
            Equal(Call("act", F.Id("rhoZero"), z), Call("identityMatrix", D(2))));
        Formula zeroNotUnit = Seq(
            Neg, Sp, Call("IsUnit", Call("zeroMatrix", D(2))));
        return Disp(Seq(
            selfConjugate, Sp, Land, Sp,
            constantIdentity, Sp, Land, Sp, zeroNotUnit));
    }

    private static Formula LowDimensionAuditFormula()
    {
        Formula emptyCase = Equal(
            Call("zeroMatrix", F.Id("Empty")),
            Call("identityMatrix", F.Id("Empty")));
        Formula oneCase = Equal(
            F.Id("rhoZeroGeneratorOne"),
            F.Id("rhoUnipotentGeneratorOne"));
        return Disp(Seq(emptyCase, Sp, Land, Sp, oneCase));
    }
}
