using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeOrbits;

internal sealed class FullRoleInvarianceOrbitFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/NormativeOrbits/FullRoleInvarianceOrbitFactorization."
            + "full_role_invariance_iff_orbit_factorization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full role invariance is canonical orbit factorization for any role carrier.",
        H("Full Role-Invariance Orbit Factorization"),
        Blocks(Describe.Lean(
            DescribeId.Create("full-role-invariance-iff-orbit-factorization"),
            DeclarationHandle.Create(Declaration),
            H("Full invariance is orbit factorization without finiteness"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A role permutation fixes the state and action coordinates and acts "
                        + "simultaneously on the actor and recipient coordinates.")),
                Paragraph(Text(
                    "For an arbitrary role carrier, invariance under every role permutation "
                        + "is equivalent to factorization through the canonical role-orbit "
                        + "projection.")),
                Paragraph(Text(
                    "The proof uses orbit equivalence and quotient soundness only. No finite "
                        + "generation premise is required."))),
            DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Times, Sp, right);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula actionType = F.Id("U");
        Formula roleType = F.Id("I");
        Formula type = F.Id("Type");
        Formula prop = F.Id("Prop");
        Formula admission = F.Id("T");
        Formula state = F.Id("x");
        Formula action = F.Id("u");
        Formula actor = F.Id("i");
        Formula recipient = F.Id("j");
        Formula permutation = SigmaLower;
        Formula permutationType = Call("Perm", roleType);
        Formula admissionType = Arrow(
            stateType,
            Arrow(actionType, Arrow(roleType, Arrow(roleType, prop))));
        Formula fullInvariant = Seq(
            Open,
            Forall, Sp, permutation, Colon, Sp, permutationType, Comma, Sp,
            Call("RoleInvariant", admission, permutation),
            Close);
        Formula tuple = Seq(
            Open,
            state, Comma, Sp,
            action, Comma, Sp,
            Open, actor, Comma, Sp, recipient, Close,
            Close);
        Formula tupleType = Product(
            stateType,
            Product(actionType, Product(roleType, roleType)));
        Formula admissionReadout = Seq(
            Open,
            Typed(tuple, tupleType), Sp, Mapsto, Sp,
            Apply(admission, state, action, actor, recipient),
            Close);
        Formula factorsThrough = Call(
            "FactorsThrough",
            admissionReadout,
            Call("roleOrbitProjection", stateType, actionType, roleType));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            stateType, Comma, Sp, actionType, Comma, Sp, roleType,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            Typed(admission, admissionType), Comma, RowBreak, Grp(),
            fullInvariant, Sp, Iff, Sp, factorsThrough, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
