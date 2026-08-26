using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class TerminalGradeDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A stabilized guarded ledger partitions its semantic statements into migrated, wall, and resident parts.",
        H("Terminal Grade Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("terminal-grade-three-way-decomposition"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/TerminalGradeDecomposition.terminal_grade_three_way_decomposition"),
                H("Terminal grades give a three-way disjoint decomposition"),
                StatementSource.FromAuthor(ThreeWayDecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a countable statement ledger take values in a finite partially ordered grade "
                        + "space, and assume each statement changes grade only finitely often after enrollment. "
                        + "The pointwise ledger-limit theorem supplies a unique terminal grading and a "
                        + "stabilization cutoff for every statement.")),
                    Paragraph(Text(
                        "Let Sem be the semantic domain, W a wall contained in Sem, T its gatekeepers, and "
                        + "Gplus the positive grades. Assume every gatekeeper remains positive, joint positivity "
                        + "of a wall statement and all gatekeepers is forbidden, and forbidden wall "
                        + "configurations never occur. The guarded-wall theorem makes every wall statement "
                        + "non-positive at every time. Evaluating at its terminal cutoff therefore keeps W "
                        + "disjoint from the terminal-positive migrated part M.")),
                    Paragraph(Text(
                        "Define M as the semantic statements whose terminal grade lies in Gplus, and define R "
                        + "as Sem with M and W removed. Elementary set extensionality gives Sem = M union W "
                        + "union R. Guarded-wall non-positivity proves M and W are disjoint, while the defining "
                        + "set difference proves that R is disjoint from each. The Boolean witness in the Lean "
                        + "module checks that all assumptions can hold simultaneously."))),
                DescribeRole.Theorem)),
        []));

    private static Formula ThreeWayDecompositionFormula()
    {
        Formula statementType = F.Id("Statement");
        Formula gradeType = F.Id("Grade");
        Formula history = F.Id("history");
        Formula positiveGrades = F.Id("positiveGrades");
        Formula semantic = F.Id("semantic");
        Formula wall = F.Id("wall");
        Formula gatekeepers = F.Id("gatekeepers");

        Formula classAssumptions = Conjoin(
            Call("Countable", statementType),
            Call("Finite", gradeType),
            Call("PartialOrder", gradeType));
        Formula repairClause = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("statement"),
            statementType,
            Call(
                "Finite",
                Call(
                    "revisionTimesFrom",
                    Call("enrolledAt", history, F.Id("statement")),
                    Call("grade", history, F.Id("statement")))));
        Formula gatekeepersPositive = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("t"), F.Id("Nat")),
                new Formula.BoundVariable(FormulaIdentifier.Create("g"), statementType),
            ],
            new Formula.Logic(
                new Formula.Relation(F.Id("g"), FormulaRelationOperator.MemberOf, gatekeepers),
                FormulaLogicOperator.Implies,
                new Formula.Relation(
                    GradeAt(history, F.Id("t"), F.Id("g")),
                    FormulaRelationOperator.MemberOf,
                    positiveGrades)));
        Formula jointPositiveForbidden = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("t"), F.Id("Nat")),
                new Formula.BoundVariable(FormulaIdentifier.Create("w"), statementType),
            ],
            new Formula.Logic(
                new Formula.Relation(F.Id("w"), FormulaRelationOperator.MemberOf, wall),
                FormulaLogicOperator.Implies,
                new Formula.Logic(
                    new Formula.Relation(
                        GradeAt(history, F.Id("t"), F.Id("w")),
                        FormulaRelationOperator.MemberOf,
                        positiveGrades),
                    FormulaLogicOperator.Implies,
                    new Formula.Logic(
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("g"),
                            statementType,
                            new Formula.Logic(
                                new Formula.Relation(
                                    F.Id("g"),
                                    FormulaRelationOperator.MemberOf,
                                    gatekeepers),
                                FormulaLogicOperator.Implies,
                                new Formula.Relation(
                                    GradeAt(history, F.Id("t"), F.Id("g")),
                                    FormulaRelationOperator.MemberOf,
                                    positiveGrades))),
                        FormulaLogicOperator.Implies,
                        Call("forbidden", F.Id("t"), F.Id("w"))))));
        Formula consistent = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("t"), F.Id("Nat")),
                new Formula.BoundVariable(FormulaIdentifier.Create("w"), statementType),
            ],
            new Formula.Logic(
                new Formula.Relation(F.Id("w"), FormulaRelationOperator.MemberOf, wall),
                FormulaLogicOperator.Implies,
                new Formula.Not(Call("forbidden", F.Id("t"), F.Id("w")))));
        Formula assumptions = Conjoin(
            new Formula.Relation(wall, FormulaRelationOperator.SubsetOf, semantic),
            gatekeepersPositive,
            jointPositiveForbidden,
            consistent);
        Formula conclusion = ConclusionFormula(
            history,
            positiveGrades,
            semantic,
            wall,
            statementType,
            gradeType);

        Formula body = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("history"),
            Call("LedgerHistory", statementType, gradeType),
            new Formula.Logic(
                repairClause,
                FormulaLogicOperator.Implies,
                new Formula.Bind(
                    FormulaQuantifier.ForAll,
                    FormulaIdentifier.Create("positiveGrades"),
                    Call("Set", gradeType),
                    new Formula.BindMany(
                        FormulaQuantifier.ForAll,
                        [
                            new Formula.BoundVariable(FormulaIdentifier.Create("semantic"), Call("Set", statementType)),
                            new Formula.BoundVariable(FormulaIdentifier.Create("wall"), Call("Set", statementType)),
                            new Formula.BoundVariable(FormulaIdentifier.Create("gatekeepers"), Call("Set", statementType)),
                        ],
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("forbidden"),
                            new Formula.TypeArrow(
                                F.Id("Nat"),
                                new Formula.TypeArrow(statementType, F.Id("Prop"))),
                            new Formula.Logic(
                                assumptions,
                                FormulaLogicOperator.Implies,
                                conclusion))))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("Statement"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("Grade"), F.Id("Type")),
            ],
            new Formula.Logic(
                classAssumptions,
                FormulaLogicOperator.Implies,
                body)));
    }

    private static Formula ConclusionFormula(
        Formula history,
        Formula positiveGrades,
        Formula semantic,
        Formula wall,
        Formula statementType,
        Formula gradeType)
    {
        Formula terminalGrade = F.Id("terminalGrade");
        Formula statement = F.Id("statement");
        Formula cutoff = F.Id("cutoff");
        Formula time = F.Id("t");
        Formula migrated = F.Id("migrated");
        Formula resident = F.Id("resident");
        Formula stability = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("statement"),
            statementType,
            new Formula.Bind(
                FormulaQuantifier.Exists,
                FormulaIdentifier.Create("cutoff"),
                F.Id("Nat"),
                new Formula.Logic(
                    new Formula.Relation(
                        Call("enrolledAt", history, statement),
                        FormulaRelationOperator.LessThanOrEqual,
                        cutoff),
                    FormulaLogicOperator.And,
                    new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("t"),
                        F.Id("Nat"),
                        new Formula.Logic(
                            new Formula.Relation(time, FormulaRelationOperator.GreaterThanOrEqual, cutoff),
                            FormulaLogicOperator.Implies,
                            new Formula.Relation(
                                GradeAt(history, time, statement),
                                FormulaRelationOperator.Equal,
                                new Formula.Apply(terminalGrade, [statement])))))));
        Formula decomposition = F.Seq(
            Open, stability, Close, Sp, Land, Sp, RowBreak, Grp(),
            migrated, Sp, Eq, Sp,
            Operatorname, Grp(F.Id("intersection")), Open,
            semantic, Comma,
            Operatorname, Grp(F.Id("preimage")), Open,
            terminalGrade, Comma, positiveGrades, Close, Close,
            Comma, Sp,
            resident, Sp, Eq, Sp, semantic, Sp, Setminus, Sp,
            Open, migrated, Sp, Operatorname, Grp(F.Id("union")), Sp, wall, Close,
            Comma, RowBreak, Grp(),
            semantic, Sp, Eq, Sp, migrated, Sp,
            Operatorname, Grp(F.Id("union")), Sp, wall, Sp,
            Operatorname, Grp(F.Id("union")), Sp, resident, Sp, Land, RowBreak, Grp(),
            Operatorname, Grp(F.Id("Disjoint")), Open, migrated, Comma, wall, Close,
            Sp, Land, Sp,
            Operatorname, Grp(F.Id("Disjoint")), Open, migrated, Comma, resident, Close,
            Sp, Land, Sp,
            Operatorname, Grp(F.Id("Disjoint")), Open, wall, Comma, resident, Close, Close);

        return F.Seq(
            Exists, Bang, Sp,
            terminalGrade, Colon, Sp,
            new Formula.TypeArrow(statementType, gradeType), Comma, Sp,
            decomposition, Dot);
    }

    private static Formula Conjoin(Formula first, params Formula[] rest)
    {
        var result = first;
        foreach (var item in rest)
        {
            result = new Formula.Logic(result, FormulaLogicOperator.And, item);
        }

        return result;
    }

    private static Formula GradeAt(Formula history, Formula time, Formula statement) =>
        Call("grade", history, statement, time);
}
