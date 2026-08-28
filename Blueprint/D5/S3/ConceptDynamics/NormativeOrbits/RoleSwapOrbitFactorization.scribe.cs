using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeOrbits;

internal sealed class RoleSwapOrbitFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/NormativeOrbits/RoleSwapOrbitFactorization."
            + "role_swap_full_invariance_orbit_factorization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pairwise role swaps generate full role invariance and canonical orbit factorization.",
        H("Role-Swap Orbit Factorization"),
        Blocks(Describe.Lean(
            DescribeId.Create("role-swap-full-invariance-orbit-factorization"),
            DeclarationHandle.Create(Declaration),
            H("Role swaps generate full invariance and orbit factorization"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The carrier of roles is finite. A role permutation fixes the state and "
                        + "action coordinates and acts simultaneously on the actor and recipient.")),
                Paragraph(Text(
                    "The first public equivalence states that invariance under every pairwise "
                        + "role swap is exactly invariance under every role permutation. The "
                        + "forward implication uses the pinned permutation-generation theorem.")),
                Paragraph(Text(
                    "The second public equivalence uses the canonical quotient projection of the "
                        + "complete state-action-role tuple. Thus the factorization clause retains "
                        + "state and action while forgetting only role names.")),
                Paragraph(Text(
                    "Pinned-library search supplied the swap-generation, orbit-quotient, and "
                        + "fiber-factorization primitives. Repository searches found no frozen "
                        + "declaration combining these two equivalences for an admission predicate."))),
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
        Formula roleInvariant = Call(
            "RoleInvariant",
            admission,
            permutation);
        Formula pairwiseInvariant = Seq(
            Open,
            Forall, Sp, actor, Comma, Sp, recipient, Colon, Sp, roleType, Comma, Sp,
            Call(
                "RoleInvariant",
                admission,
                Call("swap", actor, recipient)),
            Close);
        Formula fullInvariant = Seq(
            Open,
            Forall, Sp, permutation, Colon, Sp, permutationType, Comma, Sp,
            roleInvariant,
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
            Call("Finite", roleType), Sp, Rightarrow, RowBreak, Grp(),
            Open,
            Open, pairwiseInvariant, Sp, Iff, Sp, fullInvariant, Close,
            Sp, Land, RowBreak, Grp(),
            Open, fullInvariant, Sp, Iff, Sp, factorsThrough, Close,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
