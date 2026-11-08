using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinFactor;

internal sealed class OriginalClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete original-D H2 classification",
        H("Pinned Theorem 93.1 integration endpoint"),
        Blocks(
            Paragraph(Text("The carrier is the original real spin factor E = R × R^3 with the pinned Jordan product, cone, evaluations alpha_(m,v) for every m >= norm(v), including zero, subnormalized and unequal masses, and original norm |s| + norm(x). D is one arbitrary total E -> E -> E used in every directed Gram entry and every phase-square slot. No additivity, homogeneity, continuity, unit rows, translation neutrality, P3, NN, PY, R, CP or physical-realization premise is added.")),
            Paragraph(Text("The exact endpoint is: for every total D, the actual directed complex two-label Gram PSD condition P2, with both directed off-diagonal entries and both diagonals for every positive evaluation, together with the literal same-D plus/minus phase-square balance PB, holds if and only if there is one orientation epsilon in {plus, minus} such that D((s,x),(t,y)) = (0, epsilon times (x cross y)) for every real s,t and every original x,y. Both implications and all zero, proportional, unequal-length, unit and nonunit inputs are included.")),
            Paragraph(Text("The forward proof consumes OriginalPureRigidity.global_pure to obtain one global pure sign from only P2 and PB, then consumes OriginalResidual.all_inputs_of_pure to extend that same sign to arbitrary scalar/vector inputs. The residual proof consumes the exact finite SO(3) word theorem and moving-axis/right-word transport; it does not use density, closure or continuity of unknown D.")),
            Paragraph(Text("The reverse implication identifies the chosen orientation with the fixed Pauli product and consumes OriginalSpinConsumers.same_D_consequences. The resulting Consequences record the same-D unit and translation neutrality, real bilinearity, original-norm bounds and continuity, every finite complex Gram PSD table, and the original reassociation identity R. MatrixInterfaces records all original positive masses, the cone, the original order-unit norm and the fixed product/readout realization. These are mathematical consequences for the same D, not extra premises.")),
            Paragraph(Text("The conclusion concerns the complete specified finite spin model. A Pauli matrix representation is a mathematical realization of its products, cone, norm and evaluations. It supplies no physical preparation, instrument, channel, resource cost or realization of a complete original source.")),
            Describe.Lean(
                DescribeId.Create("original-complete-classification"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalClassification.complete_classification"),
                H("Complete P2-PB iff classification"),
                StatementSource.FromAuthor(Disp(ClassificationFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original total D, P2 D and PB D are equivalent to the existence of one Orientation epsilon, chosen globally before any input, with D a b = crossD epsilon a b for all a,b in the original E."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-complete-consequences"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalClassification.complete_consequences"),
                H("Same-D consequences of the classified orientation"),
                StatementSource.FromAuthor(Disp(ConsequencesFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D satisfying the original P2 and PB, the endpoint returns one global Orientation epsilon, its all-input crossD equality, the full Consequences structure, and the corresponding MatrixInterfaces structure. The structures retain unit and translation neutrality, real bilinearity, original-norm continuity and bounds, all finite complex Gram tables, R, all positive evaluations and masses, the cone and the original norm. No physical realization or stronger regularity is asserted."))),
                DescribeRole.Theorem))));

    private static Formula ClassificationFormula() => For(
        Iff(And(Call("P2", X("D")), Call("PB", X("D"))),
            Exists(CrossEquality(), "epsilon", X("Orientation"))),
        "D", Relation());

    private static Formula ConsequencesFormula()
    {
        var e = X("epsilon"); var d = X("D");
        var choices = new Formula.Logic(Equal(e, X("plus")),
            FormulaLogicOperator.Or, Equal(e, X("minus")));
        var result = And(choices, And(CrossEquality(),
            And(Call("Consequences", d), Call("MatrixInterfaces", Call("orientationBool", e), d))));
        return For(Implies(Call("P2", d), Implies(Call("PB", d),
            Exists(result, "epsilon", X("Orientation")))), "D", Relation());
    }

    private static Formula CrossEquality() => For(For(
        Equal(Apply(X("D"), X("a"), X("b")),
            Call("crossD", X("epsilon"), X("a"), X("b"))), "b", X("E")), "a", X("E"));
    private static Formula X(string name) => F.Id(name);
    private static Formula Relation() => new Formula.TypeArrow(X("E"),
        new Formula.TypeArrow(X("E"), X("E")));
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        Apply(Seq(Operatorname, Grp(X(name))), args);
    private static Formula For(Formula body, string name, Formula type) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(Formula body, string name, Formula type) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
