using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class AffinePartitionFlagMaximumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/heimendahlheinrichgross2022magic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The flag partition maximizes the squared sizes of affine parts outside the origin.",
        H("The affine partition flag maximum"),
        Blocks(
            Node("is-affine-partition", "Affine partitions of the punctured vector space", "isAffinePartition", IsAffinePartitionFormula(),
                "A finite family of affine subspaces is an affine partition when every part is nonempty, distinct parts are disjoint, and a vector is nonzero exactly when it belongs to one of the parts. This is the partition condition in the source's stabiliser-operation lemma (lines 986–994)."),
            Node("sq-sum", "The squared-cardinality objective", "sqSum", SqSumFormula(),
                "sqSum adds the squares of the cardinalities of the affine parts. It is the quantity appearing in the source's overlap bound (lines 1209–1217)."),
            Node("flag-cell", "A coordinate flag cell", "flagCell", FlagCellFormula(),
                "For an index i and a nonzero or zero coordinate value x, flagCell p n i x consists of vectors whose coordinates before i vanish and whose i-th coordinate equals x. It is the affine tail described by the source's first-nonzero-coordinate construction (lines 1219–1232)."),
            Node("flag-partition", "The partition by first nonzero coordinate", "flagPartition", FlagPartitionFormula(),
                "flagPartition is the image of all pairs (i,x) with i in Fin n and x a nonzero element of ZMod p under the flag-cell construction. It encodes the measurement procedure and induced partition in the source (lines 1219–1232)."),
            Node("flag-value", "The value of the flag partition", "flagValue", FlagValueFormula(),
                "flagValue p n is the finite sum ∑ₖ₍₀≤k<n₎ (p−1)p^(2k), the squared-cardinality value stated for the flag partition in the source (lines 1233–1237)."),
            Node("claim", "The flag partition maximum conjecture", "claim", ClaimFormula(),
                "For every prime p and natural n, the flag cells form an affine partition of the nonzero vectors, their squared-cardinality sum is flagValue, and every affine partition has no larger squared-cardinality sum. This is the source's maximising-measurement conjecture under the formal reading that all affine partitions are admitted (lines 1215–1232)."),
            Describe.Lean(
                DescribeId.Create("affine-partition-flag-maximum-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The affine partition flag maximum is proved"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The proof first identifies the cardinality of every nonempty affine part with "
                        + "p raised to the finrank of its direction, and uses disjointness and coverage "
                        + "to show that the part sizes sum to p^n−1. It then introduces a digit potential "
                        + "formed from the base-p digits of s. Its step, affine, and one-unit identities yield "
                        + "the power inequality p^(2k) plus the potential of s−p^k is at most the potential of s whenever "
                        + "p^k ≤ s. Induction over a finite family of powers of p gives the squared-size "
                        + "bound by the potential of the total size, and induction on n evaluates the potential at p^n−1 "
                        + "as flagValue p n.")),
                    Paragraph(Text(
                        "The flag-cell center Pi.single i x proves nonemptiness; the least nonzero coordinate "
                        + "of a vector gives the unique flag index, proving disjointness and covering exactly "
                        + "the nonzero vectors. An explicit finite equivalence identifies each cell with the "
                        + "free coordinates after i, so its cardinality is p^(n−1−i). Summing over i and over "
                        + "the p−1 nonzero coordinate values gives flagValue. Combining these facts with the "
                        + "digit-potential bound proves claim (arXiv TeX lines 1219–1245)."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula, string prose) =>
        Describe.Lean(
            DescribeId.Create("affine-partition-flag-maximum-" + id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);

    private static Formula Qualified(params string[] parts) =>
        Seq(parts.SelectMany((part, index) => index == 0
            ? new Formula[] { Operatorname, Grp(X(part)) }
            : new Formula[] { Dot, Operatorname, Grp(X(part)) }).ToArray());

    private static Formula Owner(string name) => Qualified(
        "D5", "S3", "Quantum", "Magic", "AffinePartitionFlagMaximum", name);

    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula LocalCall(string name, params Formula[] arguments) =>
        App(Owner(name), arguments);

    private static Formula QCall(string owner, string name, params Formula[] arguments) =>
        App(Qualified(owner, name), arguments);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));

    private static Formula ExistsQ(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));

    private static Formula LambdaOf(Formula variable, Formula type, Formula body) =>
        Parenthesized(Seq(Lambda, Sp, Typed(variable, type), Sp, Mapsto, Sp, body));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Nats => Seq(Mathbb, Grp(X("N")));

    private static Formula SetType(Formula type) => App(Qualified("Set"), type);

    private static Formula CoeSet(Formula value, Formula type) => Typed(value, SetType(type));

    private static Formula CoeSort(Formula value, Formula type) =>
        App(Qualified("CoeSort", "coe"), CoeSet(value, type));

    private static Formula ZMod(Formula p) => App(Qualified("ZMod"), p);

    private static Formula Fin(Formula n) => App(Qualified("Fin"), n);

    private static Formula Vector(Formula p, Formula n) => Arrow(Fin(n), ZMod(p));

    private static Formula Affine(Formula field, Formula carrier) =>
        App(Qualified("AffineSubspace"), field, carrier);

    private static Formula Parts(Formula p, Formula n) =>
        App(Qualified("Finset"), Affine(ZMod(p), Vector(p, n)));

    private static Formula Prime(Formula p) => App(Qualified("Nat", "Prime"), p);

    private static Formula PrimeInstance(Formula p) =>
        Seq(OpenBracket, App(Qualified("Fact"), Prime(p)), CloseBracket);

    private static Formula PrimeScope(Formula p, Formula n, Formula body) =>
        Seq(Forall, Sp, Typed(p, Nats), Comma, Sp, PrimeInstance(p), Sp,
            All(n, Nats, body));

    private static Formula SumIn(Formula variable, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Member(variable, set)), Sp, Parenthesized(body));

    private static Formula NatCard(Formula value, Formula carrier) =>
        QCall("Nat", "card", CoeSort(value, carrier));

    private static Formula Nonempty(Formula value, Formula carrier) =>
        QCall("Set", "Nonempty", CoeSet(value, carrier));

    private static Formula Disjoint(Formula left, Formula right, Formula carrier) =>
        App(Qualified("Disjoint"), CoeSet(left, carrier), CoeSet(right, carrier));

    private static Formula Subtype(Formula type, Formula variable, Formula predicate) =>
        App(Qualified("Subtype"), LambdaOf(variable, type, predicate));

    private static Formula IsAffinePartitionFormula()
    {
        Formula p = X("p"), n = X("n"), parts = X("parts"), k = X("k"), l = X("l"), v = X("v");
        Formula vector = Vector(p, n);
        Formula affine = Affine(ZMod(p), vector);
        Formula first = All(k, affine,
            Implies(Member(k, parts), Nonempty(k, vector)));
        Formula disjoint = All(k, affine,
            Implies(Member(k, parts),
                All(l, affine,
                    Implies(Member(l, parts),
                        Implies(NotEqual(k, l), Disjoint(k, l, vector))))));
        Formula cover = All(v, vector,
            Iff(NotEqual(v, Typed(D(0), vector)),
                ExistsQ(k, affine, And(Member(k, parts),
                    Member(v, CoeSet(k, vector))))));
        return PrimeScope(p, n,
            All(parts, Parts(p, n),
                Equal(LocalCall("isAffinePartition", p, n, parts),
                    And(first, And(disjoint, cover)))));
    }

    private static Formula SqSumFormula()
    {
        Formula p = X("p"), n = X("n"), parts = X("parts"), k = X("k");
        Formula vector = Vector(p, n);
        Formula affine = Affine(ZMod(p), vector);
        Formula body = SumIn(k, parts, new Formula.Power(NatCard(k, vector), D(2)));
        return Seq(Forall, Sp, Typed(p, Nats), Comma, Sp, Typed(n, Nats), Comma, Sp,
            PrimeInstance(p), Sp,
            All(parts, Parts(p, n), Equal(LocalCall("sqSum", p, n, parts), body)));
    }

    private static Formula FlagCellFormula()
    {
        Formula p = X("p"), n = X("n"), i = X("i"), x = X("x"), v = X("v"), j = X("j");
        Formula vector = Vector(p, n);
        Formula carrier = Seq(OpenBrace, v, Colon, Sp, vector, Sp, Mid, Sp,
            And(All(j, Fin(n), Implies(LessThan(j, i),
                Equal(App(v, j), Typed(D(0), ZMod(p))))),
                Equal(App(v, i), x)), CloseBrace);
        return PrimeScope(p, n,
            All(i, Fin(n), All(x, ZMod(p),
                Equal(CoeSet(LocalCall("flagCell", p, n, i, x), vector), carrier))));
    }

    private static Formula FlagPartitionFormula()
    {
        Formula p = X("p"), n = X("n"), a = X("a"), i = X("i"), x = X("x");
        Formula vector = Vector(p, n);
        Formula affine = Affine(ZMod(p), vector);
        Formula nonzero = NotEqual(x, Typed(D(0), ZMod(p)));
        Formula subtype = Subtype(ZMod(p), x, nonzero);
        Formula pair = App(Qualified("Prod"), Fin(n), subtype);
        Formula index = App(Qualified("Prod", "fst"), a);
        Formula value = App(Qualified("Subtype", "val"),
            App(Qualified("Prod", "snd"), a));
        Formula image = QCall("Finset", "image",
            LambdaOf(a, pair, LocalCall("flagCell", p, n, index, value)),
            QCall("Finset", "univ"));
        return PrimeScope(p, n,
            Equal(LocalCall("flagPartition", p, n), image));
    }

    private static Formula FlagValueFormula()
    {
        Formula p = X("p"), n = X("n"), k = X("k");
        Formula term = new Formula.Binary(
            new Formula.Binary(p, FormulaBinaryOperator.Subtract, D(1)),
            FormulaBinaryOperator.Multiply,
            new Formula.Power(p, new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, k)));
        return All(p, Nats, All(n, Nats,
            Equal(LocalCall("flagValue", p, n), SumIn(k, QCall("Finset", "range", n), term))));
    }

    private static Formula ClaimFormula()
    {
        Formula p = X("p"), n = X("n"), parts = X("parts");
        Formula partition = LocalCall("isAffinePartition", p, n, LocalCall("flagPartition", p, n));
        Formula value = Equal(LocalCall("sqSum", p, n, LocalCall("flagPartition", p, n)),
            LocalCall("flagValue", p, n));
        Formula bound = All(parts, Parts(p, n),
            Implies(LocalCall("isAffinePartition", p, n, parts),
                LessEqual(LocalCall("sqSum", p, n, parts), LocalCall("flagValue", p, n))));
        return PrimeScope(p, n, And(partition, And(value, bound)));
    }
}
