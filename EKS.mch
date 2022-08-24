MACHINE           EKS
/* This B Machine models a simplified electronic key system.
*/
SETS              BOOK; USER; STATUS = {locked, unlocked}; AUTHOR; YEAR

VARIABLES         books, users, users_has_login, users_member, access, r_status, author, publish_in, borrowed, has_borrowed

PROPERTIES		  card(BOOK) = 5

INVARIANT         books : POW(BOOK) & 
                  users : POW(USER) & 
		  users_has_login : POW(USER) & 
		  users_member : POW(USER) & 
                  access : BOOK <-> USER & 
		  author: BOOK <-> AUTHOR &
		  publish_in: BOOK <-> YEAR &
                  r_status : USER --> STATUS &
                  dom(access) <: books &
                  ran(access) <: users &
       		  borrowed : POW(BOOK) &
     		  has_borrowed: USER <-> BOOK 

INITIALISATION    books := {};
                  users := {};
		  users_has_login := {};
		  users_member := {};
                  access := {};
		  author := BOOK * {};
		  publish_in := BOOK * {};
                  r_status := USER * {locked};
		  borrowed :={};
   		  has_borrowed:= {}

OPERATIONS
  addbook(kk, aa, yy) = PRE kk:BOOK & kk /: books & aa : AUTHOR & yy:YEAR THEN books := books \/ {kk}; author := author \/ {kk |-> aa}; publish_in := publish_in \/ {kk |-> yy} END;

  deletebook(kk) = PRE kk : books & {kk} <| access = {} THEN books := books - {kk}; author := {kk} <<| author; publish_in := {kk} <<| publish_in  END;

  adduser(rr) = PRE rr:USER & rr /: users THEN users := users \/ {rr} END;

  deleteuser(rr) = PRE rr : users & access |> {rr} = {} THEN users := users - {rr} END;

  userlogin (uu) = PRE uu : users & uu/: users_has_login THEN users_has_login := users_has_login \/ {uu} END;

  buymember (uu) = PRE uu : users & uu: users_has_login & uu: users_has_login & uu/: users_member THEN users_member := users_member \/ {uu} END;

  userlogout (uu) = PRE uu : users & uu: users_has_login THEN users_has_login := users_has_login - {uu} END;

  borrowbook(kk,uu) = PRE kk:BOOK & kk:books & kk/: borrowed & uu:users & uu:users_has_login THEN borrowed := borrowed \/ {kk}; has_borrowed := has_borrowed\/{uu |->kk}END;

  output <-- Search_author(aa) = PRE books /= {}& aa:AUTHOR THEN output:=author |> {aa} END;

  output <-- Search_year(yy) = PRE books /= {}& yy:YEAR THEN output:=publish_in |> {yy} END


END
