using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeStructure;

internal sealed class TranspositionOrbitFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/NormativeStructure/TranspositionOrbitFactorization."
            + "transposition_orbit_factorization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Swap invariance is full role invariance and canonical orbit factorization.",
        H("Transposition Invariance and Orbit Factorization"),
        Blocks(Describe.Lean(
            DescribeId.Create("transposition-orbit-factorization"),
            DeclarationHandle.Create(Declaration),
            H("Transpositions generate full role invariance"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A permutation acts simultaneously on the actor and recipient coordinates "
                        + "while leaving the state and action coordinates fixed.")),
                Paragraph(Text(
                    "For a finite role carrier, invariance under every transposition is equivalent "
                        + "to invariance under every permutation. The proof applies Mathlib's "
                        + "finite permutation induction directly.")),
                Paragraph(Text(
                    "Full invariance is also equivalent to factorization through Mathlib's "
                        + "canonical orbit-relation quotient for this action. The finite-role "
                        + "instance is displayed as a premise."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Product(params Formula[] factors)
    {
        var items = new List<Formula>();
        for (var index = 0; index < factors.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Times, Sp]);
            items.Add(factors[index]);
        }
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula prop = F.Id("Prop");
        Formula state = F.Id("X");
        Formula action = F.Id("U");
        Formula role = F.Id("I");
        Formula predicate = F.Id("T");
        Formula sigma = F.Id("sigma");
        Formula actor = F.Id("i");
        Formula recipient = F.Id("j");
        Formula record = F.Id("z");
        Formula actionMap = F.Id("R");
        Formula projection = F.Id("p");
        Formula recordType = Product(state, action, role, role);
        Formula permType = Call("Perm", role);
        Formula relabeled = Apply(actionMap, sigma, record);
        Formula invariantBody = new Formula.Logic(
            Apply(predicate, relabeled),
            FormulaLogicOperator.Iff,
            Apply(predicate, record));
        Formula swapInvariant = Seq(
            Forall, Sp,
            Typed(actor, role), Comma, Sp,
            Typed(recipient, role), Comma, Sp,
            Typed(record, recordType), Comma, Sp,
            new Formula.Logic(
                Apply(
                    predicate,
                    Apply(actionMap, Call("swap", actor, recipient), record)),
                FormulaLogicOperator.Iff,
                Apply(predicate, record)));
        Formula fullInvariant = Seq(
            Forall, Sp,
            Typed(sigma, permType), Comma, Sp,
            Typed(record, recordType), Comma, Sp,
            invariantBody);
        Formula orbitQuotient = Call(
            "Quotient",
            Call("orbitRel", permType, recordType, actionMap));
        Formula factorization = Seq(
            Exists, Sp,
            Typed(F.Id("D"), Arrow(orbitQuotient, prop)), Comma, Sp,
            predicate, Sp, Eq, Sp,
            Call("compose", F.Id("D"), projection));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(state, Comma, Sp, action, Comma, Sp, role), type),
            Comma, RowBreak, Grp(),
            Typed(predicate, Arrow(recordType, prop)), Comma, RowBreak, Grp(),
            Typed(
                actionMap,
                Arrow(permType, Arrow(recordType, recordType))),
            Sp, Colon, Eq, Sp,
            Lambda, Sp, Typed(sigma, permType), Comma, Sp,
            Lambda, Sp, Typed(record, recordType), Comma, Sp,
            Call("relabelRoles", sigma, record),
            Comma, RowBreak, Grp(),
            Typed(projection, Arrow(recordType, orbitQuotient)),
            Sp, Colon, Eq, Sp,
            Call("orbitProjection", permType, recordType, actionMap),
            Comma, RowBreak, Grp(),
            Call("Finite", role), Sp, Rightarrow, RowBreak, Grp(),
            OpenBracket,
            Open,
            Open, swapInvariant, Close,
            Sp, Iff, Sp,
            Open, fullInvariant, Close,
            Close,
            Sp, Land, RowBreak, Grp(),
            Open,
            Open, fullInvariant, Close,
            Sp, Iff, Sp,
            Open, factorization, Close,
            Close,
            CloseBracket, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
