using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeStarContactsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarContacts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The concrete remaining stars are disjoint and each meets the actual two-star core in one full circle whose native b edge survives the core cuts.",
        H("Concrete Remaining Native Star Contacts"),
        Blocks(
            Paragraph(Text(
                "For j in Fin(m-2), contactAnchor(j) is the actual permutation tuple "
                + "(1,...,j+1,m,j+2,...,m-1,0). Thus the finite indices enumerate the literal "
                + "insertion labels 1 through m-2. SupplierStar(z) fixes the circular residual tuple "
                + "obtained by deleting z's last label, up to whole reversal. Circle(z) fixes the "
                + "complete actual tuple up to rotation and reversal. These domains are specified "
                + "before choosing any path or Hamilton cycle.")),
            Describe.Lean(DescribeId.Create("contact-stars-pairwise-disjoint"),
                DeclarationHandle.Create(Prefix + "contact_stars_pairwise_disjoint"),
                H("Distinct Concrete Insertion Stars Are Disjoint"),
                StatementSource.FromAuthor(PairwiseFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every contact star deletes 0. In its residual circle the neighbours of m are "
                    + "j+1 and j+2. A common actual configuration would identify the residual cycles "
                    + "either directly or with their orientations reversed. Direct equality forces "
                    + "the two finite indices to agree; reverse equality contradicts the two "
                    + "consecutive neighbour equations. The claim concerns the complete stars."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("contact-star-lower-disjoint"),
                DeclarationHandle.Create(Prefix + "contact_star_lower_disjoint"),
                H("The Lower Supplier Misses Every Remaining Star"),
                StatementSource.FromAuthor(LowerFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For m at least four, the lower a*c supplier also deletes 0, but its residual "
                    + "neighbours of m are 1 and m-1. These cannot equal the consecutive contact "
                    + "neighbours in either orientation. This excludes the full lower star, including "
                    + "both shared core circles."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("contact-star-upper-intersection"),
                DeclarationHandle.Create(Prefix + "contact_star_upper_intersection"),
                H("The Upper Supplier Has Exactly the Actual Contact Circle"),
                StatementSource.FromAuthor(IntersectionFormula(false)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The literal contact tuple is the rotation by m-1-j of upperPort(j). Hence "
                    + "its complete circle is exactly the corresponding upper noncore circle and "
                    + "belongs to its contact star. The existing actual T circle partition places "
                    + "every upper vertex in a lower-owned circle or an upper noncore circle. Lower "
                    + "disjointness excludes the first case, and pairwise star disjointness forces "
                    + "the second circle's owner to be j. Both directions retain the full circle."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("contact-star-core-intersection"),
                DeclarationHandle.Create(Prefix + "contact_star_core_intersection"),
                H("The Two-Star Core Meets the New Star in One Complete Circle"),
                StatementSource.FromAuthor(IntersectionFormula(true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "CoreDomain is the actual union of the lower a*c and upper tau*a*c deletion "
                    + "stars, where tau swaps labels 0 and m. The lower intersection is empty "
                    + "and the upper intersection is the "
                    + "complete contact circle. This earns the one-contact domain hypothesis "
                    + "required by the existing actual native E grafting theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("contact-b-edge-not-deleted"),
                DeclarationHandle.Create(Prefix + "contact_b_edge_not_deleted"),
                H("The Actual Contact b Edge Survives the Literal Core Cuts"),
                StatementSource.FromAuthor(EdgeFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "CoreDeletedEdge is the independently specified literal T cut inventory. "
                    + "Both endpoints of every lower-owned cut belong to the lower supplier, "
                    + "which misses the contact star. Both endpoints of every upper cut have "
                    + "last label m, whereas the contact anchor has last label 0. Equality of "
                    + "undirected edges would identify the contact anchor with one of those "
                    + "endpoints and contradict the corresponding invariant. The existing "
                    + "core edge inventory therefore retains this same actual contact edge."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "These results classify the concrete remaining graft contacts and their old core "
                + "edges for every m at least four. They do not assert full second-layer coverage, "
                + "marked-path recombination, or the all-size recursive Hamiltonicity conclusion; "
                + "those require their own actual support and edge arguments.")))));

    private static Formula PairwiseFormula()
    {
        Formula m = F.Id("m"), i = F.Id("i"), j = F.Id("j");
        Formula body = Call("Disjoint", Call("starDomain", Call("contactAnchor", i)),
            Call("starDomain", Call("contactAnchor", j)));
        return Disp(All("m", Call("Nat"), All("i", Indices(m), All("j", Indices(m),
            Implies(Not(Eq(i, j)), body)))));
    }

    private static Formula LowerFormula()
    {
        Formula m = F.Id("m"), j = F.Id("j");
        Formula ac = Call("mul", Call("a", m), Call("c", m));
        Formula body = Call("Disjoint", Call("starDomain", Call("contactAnchor", j)),
            Call("starDomain", ac));
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m), All("j", Indices(m), body))));
    }

    private static Formula IntersectionFormula(bool core)
    {
        Formula m = F.Id("m"), j = F.Id("j"), v = F.Id("v");
        Formula contact = Call("contactAnchor", j);
        Formula supplier = Call("SupplierStar", contact, v);
        Formula upper = Call("mul", Call("swap", D(0), Call("last", m)),
            Call("mul", Call("a", m), Call("c", m)));
        Formula old = core ? Call("CoreDomain", m, v) : Call("SupplierStar", upper, v);
        Formula common = core ? And(old, supplier) : And(supplier, old);
        Formula body = new Formula.Logic(common, FormulaLogicOperator.Iff, Call("Circle", contact, v));
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m), All("j", Indices(m),
            All("v", Call("Configuration", m), body)))));
    }

    private static Formula EdgeFormula()
    {
        Formula m = F.Id("m"), j = F.Id("j");
        Formula contact = Call("contactAnchor", j);
        Formula edge = Call("Sym2", contact, Call("mul", contact, Call("b", m)));
        Formula body = Not(Call("CoreDeletedEdge", m, edge));
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m), All("j", Indices(m), body))));
    }

    private static Formula Indices(Formula m) => Call("Fin", Call("sub", m, D(2)));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
