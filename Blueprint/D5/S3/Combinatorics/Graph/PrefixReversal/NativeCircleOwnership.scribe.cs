using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeCircleOwnershipDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual two T supplier stars intersect in exactly two core circles and their union has a unique complete circle owner.",
        H("Native Circle Ownership"),
        Blocks(
            CoordinateAPI("lowerPort", "The Literal Lower Noncore Ports", "The lower port is the actual product a*c*(b*c)^j used by the T core and contact classification.", true),
            CoordinateAPI("upperPort", "The Literal Upper Noncore Ports", "The upper port exchanges labels zero and m in the corresponding lower port.", true),
            CoordinateAPI("native_nextLabel_apply", "Next Label at an Actual Position", "The cyclic next label is the configuration evaluated at the successor position modulo m+1.", false),
            CoordinateAPI("native_prevLabel_apply", "Previous Label at an Actual Position", "The cyclic previous label is the configuration evaluated at the predecessor position modulo m+1.", false),
            CoordinateAPI("native_bc_pow_val", "Every Prefix Rotation Power on Positions", "For m at least two, each power of b*c rotates the first m positions modulo m and fixes the last position.", false),
            CoordinateAPI("native_ac_apply_val", "The Actual Two-Reversal Port Coordinates", "For m at least three, the product a*c has the displayed pointwise position formula.", false),
            CoordinateAPI("native_lowerPort_val", "Lower Port Coordinates", "For m at least three, each lower port has the displayed modular pointwise formula on positions below m.", false),
            CoordinateAPI("native_lower_m_position", "The Last Label Position in a Lower Port", "For m at least four, label m occurs at the explicitly computed position m-2-j.", false),
            CoordinateAPI("native_lower_next", "The Next Label at m in a Lower Port", "For m at least four, the cyclic next label of m in every lower noncore port is one.", false),
            CoordinateAPI("native_lower_prev", "The Previous Label at m in a Lower Port", "For m at least four, the cyclic previous label of m in every lower noncore port is m-1.", false),
            CoordinateAPI("native_lower_last", "The Lower Port Terminal Label", "For m at least four, every lower noncore port ends with label zero.", false),
            CoordinateAPI("native_upper_last", "The Upper Port Terminal Label", "For m at least four, every upper noncore port ends with label m.", false),
            CoordinateAPI("native_upper_next", "The Next Label at m in an Upper Port", "For m at least four, the cyclic next label of m in upper port j is j+2.", false),
            CoordinateAPI("native_upper_prev", "The Previous Label at m in an Upper Port", "For m at least four, the cyclic previous label of m is one at j=0 and j+1 otherwise.", false),
            CoordinateAPI("native_t_circle_owner_unique", "Actual T Circle Owner Uniqueness", "For m at least four, two indexed T circle domains containing the same actual configuration have the same owner. This is consumed by the concrete contact edge classification.", false),
            Paragraph(Text(
                "The ownership argument compares actual tuple cycles. Rotation preserves both cyclic neighbours "
                + "of every label and whole reversal exchanges next with previous. Existing coordinate equivalence "
                + "then proves that two distinct insertion gaps cannot share a complete circle.")),
            Describe.Lean(DescribeId.Create("circle-gap-disjoint"),
                DeclarationHandle.Create(Prefix + "native_circle_gap_disjoint"),
                H("Distinct Insertion Gaps Have Disjoint Circle Domains"),
                StatementSource.FromAuthor(Formula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is an actual support statement for the F2 supplier decomposition. It uses the literal "
                    + "rotation/reversal quotient and does not infer ownership from a chosen path."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("star-circle-partition"),
                DeclarationHandle.Create(Prefix + "native_star_circle_partition"),
                H("The Deletion Star Is Exactly Its Complete Insertion-Gap Circles"),
                StatementSource.FromAuthor(StarPartitionFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For m at least three, deleting the last label of the supplier tuple defines "
                    + "the whole star independently of any walk. A configuration belongs to that "
                    + "star exactly when it belongs to one of the m complete native gap circles. "
                    + "The existing star and circle coordinate equivalences prove both directions. "
                    + "Together with gap disjointness this gives the support partition used when "
                    + "grafting a new star onto an actual cycle through one contact circle."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("circle-neighbours"),
                DeclarationHandle.Create(Prefix + "circle_neighbours"),
                H("Circle Ownership Preserves the Unordered Cyclic Neighbours"),
                StatementSource.FromAuthor(NeighbourFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Actual tuple rotations preserve next and previous labels, while whole reversal exchanges "
                    + "them. This invariant is the reusable boundary for cross-supplier ownership."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("t-cross-circle-disjoint"),
                DeclarationHandle.Create(Prefix + "native_t_cross_circle_disjoint"),
                H("The Two Native T Suppliers Have Disjoint Circle Domains"),
                StatementSource.FromAuthor(TCrossFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every m at least four, the lower ports a*c*(bc)^i and the upper ports "
                    + "swap(0,last)*a*c*(bc)^j have disjoint complete rotation-and-reversal circle "
                    + "domains. At the label m, the lower neighbours are 1 and m-1, whereas the upper "
                    + "neighbours are j+2 and either 1 or j+1; the unordered-neighbour invariant then "
                    + "gives the arithmetic contradiction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("t-core-intersection"),
                DeclarationHandle.Create(Prefix + "native_t_core_intersection"),
                H("The Two Complete Supplier Stars Intersect Exactly in Their Core Circles"),
                StatementSource.FromAuthor(CoreFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two stars are defined independently by actual deletion of the label in the last position "
                    + "of a*c or swap(0,last)*a*c. Their intersection consists precisely of the complete circles "
                    + "based at the identity and swap(0,last). The two final insertion gaps are computed pointwise; "
                    + "all other shared ownership is excluded by the actual cross-circle theorem. This supplies "
                    + "the two core domains required by the F2 splice, without assuming a path partition."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("t-circle-partition"),
                DeclarationHandle.Create(Prefix + "native_t_circle_partition"),
                H("The Full Two-Star Union Has Exactly One Complete Circle Owner"),
                StatementSource.FromAuthor(PartitionFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cut-owner index is Fin(m) plus Fin(m-2). Its first family comprises all lower insertion "
                    + "gaps, including the two shared cores; its second family comprises just the upper noncore "
                    + "ports. Every actual vertex in the independently specified union belongs to exactly one "
                    + "complete indexed circle. Full gap exhaustion supplies existence, and the earned core "
                    + "classification and disjointness supply uniqueness. This is a support partition; actual "
                    + "F2 path splicing and the higher marked-path induction remain separate obligations."))),
                DescribeRole.Theorem))));

    private static Formula CoordinateFormula(string selector)
    {
        Formula m = F.Id("m"), z = F.Id("z"), i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        Formula n = Call("add", m, D(1)), config = Call("Configuration", m), fin = Call("Fin", n);
        Formula iv = Call("val", i), jv = Call("val", j), last = Call("last", m);
        Formula a = Call("a", m), b = Call("b", m), c = Call("c", m);
        Formula lower = Call("lowerPort", j), upper = Call("upperPort", j);
        Formula mod = Call("mod", Call("add", iv, jv), m);
        Formula ports(Formula body) => All("j", Call("Fin", Call("sub", m, D(2))), body);
        Formula bounded(Formula body) => Implies(Le(D(4), m), ports(body));
        Formula apply(Formula f, Formula x) => Call("apply", f, x);
        Formula value(Formula f, Formula x) => Call("val", apply(f, x));
        Formula lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
        Formula body = selector switch
        {
            "lowerPort" => ports(Eq(lower, Call("mul", Call("mul", a, c), Call("pow", Call("mul", b, c), jv)))),
            "upperPort" => ports(Eq(upper, Call("mul", Call("swap", D(0), last), lower))),
            "native_nextLabel_apply" => All("z", config, All("i", fin,
                Eq(Call("nextLabel", z, apply(z, i)), apply(z, Call("mkFin", Call("mod", Call("add", iv, D(1)), n), n))))),
            "native_prevLabel_apply" => All("z", config, All("i", fin,
                Eq(Call("prevLabel", z, apply(z, i)), apply(z, Call("mkFin", Call("mod", Call("add", iv, m), n), n))))),
            "native_bc_pow_val" => Implies(Le(D(2), m), All("k", Call("Nat"), All("i", fin,
                Eq(value(Call("pow", Call("mul", b, c), k), i),
                    Call("ite", lt(iv, m), Call("mod", Call("add", iv, k), m), iv))))),
            "native_ac_apply_val" => Implies(Le(D(3), m), All("i", fin,
                Eq(value(Call("mul", a, c), i), Call("ite", lt(iv, Call("sub", m, D(1))),
                    Call("add", iv, D(2)), Call("sub", m, iv))))),
            "native_lowerPort_val" => Implies(Le(D(3), m), ports(All("i", fin, Implies(lt(iv, m),
                Eq(value(lower, i), Call("ite", lt(mod, Call("sub", m, D(1))),
                    Call("add", mod, D(2)), Call("sub", m, mod))))))),
            "native_lower_m_position" => bounded(Eq(apply(lower,
                Call("mkFin", Call("sub", Call("sub", m, D(2)), jv), n)), last)),
            "native_lower_next" => bounded(Eq(Call("val", Call("nextLabel", lower, last)), D(1))),
            "native_lower_prev" => bounded(Eq(Call("val", Call("prevLabel", lower, last)), Call("sub", m, D(1)))),
            "native_lower_last" => bounded(Eq(apply(lower, last), D(0))),
            "native_upper_last" => bounded(Eq(apply(upper, last), last)),
            "native_upper_next" => bounded(Eq(Call("val", Call("nextLabel", upper, last)), Call("add", jv, D(2)))),
            "native_upper_prev" => bounded(Eq(Call("val", Call("prevLabel", upper, last)),
                Call("ite", Eq(jv, D(0)), D(1), Call("add", jv, D(1))))),
            "native_t_circle_owner_unique" => OwnerFormula(m),
            _ => throw new System.ArgumentOutOfRangeException(nameof(selector))
        };
        return Disp(All("m", Call("Nat"), body));
    }

    private static Formula OwnerFormula(Formula m)
    {
        Formula v = F.Id("v"), p = F.Id("p"), q = F.Id("q");
        Formula owners = Call("Sum", Call("Fin", m), Call("Fin", Call("sub", m, D(2))));
        Formula owns(Formula x) => Call("Circle", Call("tCircleAnchor", x), v);
        return Implies(Le(D(4), m), All("v", Call("Configuration", m),
            All("p", owners, All("q", owners, Implies(And(owns(p), owns(q)), Eq(p, q))))));
    }

    private static DocumentBlock CoordinateAPI(string selector, string title, string meaning, bool definition) =>
        Describe.Lean(DescribeId.Create(selector.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title), StatementSource.FromAuthor(CoordinateFormula(selector)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(meaning))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula Formula()
    {
        Formula m = F.Id("m"), z = F.Id("z"), i = F.Id("i"), j = F.Id("j");
        Formula left = Call("gapAnchor", z, i), right = Call("gapAnchor", z, j);
        Formula body = Call("Disjoint", Call("circleDomain", left), Call("circleDomain", right));
        return Disp(All("m", Call("Nat"), Implies(Le(D(3), m),
            All("z", Call("Configuration", m), All("i", Call("Fin", m), All("j", Call("Fin", m),
                    Implies(Not(Eq(i, j)), body)))))));
    }

    private static Formula StarPartitionFormula()
    {
        Formula m = F.Id("m"), z = F.Id("z"), v = F.Id("v"), i = F.Id("i");
        Formula star = Call("Star", Call("apply", z, Call("last", m)), Call("residualList", z), v);
        Formula circles = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("i"),
            Call("Fin", m), Call("Circle", Call("gapAnchor", z, i), v));
        Formula body = new Formula.Logic(star, FormulaLogicOperator.Iff, circles);
        return Disp(All("m", Call("Nat"), Implies(Le(D(3), m),
            All("z", Call("Configuration", m), All("v", Call("Configuration", m), body)))));
    }

    private static Formula NeighbourFormula()
    {
        Formula m = F.Id("m"), z = F.Id("z"), v = F.Id("v"), x = F.Id("x");
        Formula same = And(Eq(Call("nextLabel", v, x), Call("nextLabel", z, x)),
            Eq(Call("prevLabel", v, x), Call("prevLabel", z, x)));
        Formula rev = And(Eq(Call("nextLabel", v, x), Call("prevLabel", z, x)),
            Eq(Call("prevLabel", v, x), Call("nextLabel", z, x)));
        Formula fin = Call("Fin", Call("add", m, D(1)));
        return Disp(All("m", Call("Nat"), All("z", Call("Configuration", m),
            All("v", Call("Configuration", m), All("x", fin,
                Implies(Call("Circle", z, v), Or(same, rev)))))));
    }

    private static Formula TCrossFormula()
    {
        Formula m = F.Id("m"), i = F.Id("i"), j = F.Id("j"), v = F.Id("v");
        Formula ac = Call("mul", Call("a", m), Call("c", m));
        Formula bc = Call("mul", Call("b", m), Call("c", m));
        Formula lower(Formula k) => Call("mul", ac, Call("pow", bc, Call("val", k)));
        Formula upper(Formula k) => Call("mul", Call("swap", D(0), Call("last", m)), lower(k));
        Formula lowerDomain = Call("circleDomain", lower(i));
        Formula upperDomain = Call("circleDomain", upper(j));
        Formula body = Call("Disjoint", lowerDomain, upperDomain);
        Formula fin = Call("Fin", Call("sub", m, D(2)));
        Formula sets = All("i", fin, All("j", fin, body));
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m), sets)));
    }

    private static Formula CoreFormula()
    {
        Formula m = F.Id("m"), v = F.Id("v");
        Formula ac = Call("mul", Call("a", m), Call("c", m));
        Formula swap = Call("swap", D(0), Call("last", m));
        Formula upper = Call("mul", swap, ac);
        Formula star(Formula z) => Call("Star", Call("apply", z, Call("last", m)),
            Call("residualList", z), v);
        Formula common = And(star(ac), star(upper));
        Formula cores = Or(Call("Circle", D(1), v), Call("Circle", swap, v));
        Formula body = new Formula.Logic(common, FormulaLogicOperator.Iff, cores);
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m),
            All("v", Call("Configuration", m), body))));
    }

    private static Formula PartitionFormula()
    {
        Formula m = F.Id("m"), v = F.Id("v"), p = F.Id("p"), q = F.Id("q");
        Formula ac = Call("mul", Call("a", m), Call("c", m));
        Formula swap = Call("swap", D(0), Call("last", m));
        Formula upper = Call("mul", swap, ac);
        Formula star(Formula z) => Call("Star", Call("apply", z, Call("last", m)),
            Call("residualList", z), v);
        Formula owners = Call("Sum", Call("Fin", m), Call("Fin", Call("sub", m, D(2))));
        Formula owns(Formula x) => Call("Circle", Call("tCircleAnchor", x), v);
        Formula unique = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("p"),
            owners, And(owns(p), All("q", owners, Implies(owns(q), Eq(q, p)))));
        Formula body = new Formula.Logic(Or(star(ac), star(upper)), FormulaLogicOperator.Iff, unique);
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m),
            All("v", Call("Configuration", m), body))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Not(Formula x) => new Formula.Not(x);
    private static Formula Implies(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula Or(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Or, r);
}
