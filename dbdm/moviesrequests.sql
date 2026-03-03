select name_reviewer from reviewers where id_reviewer = 205;

select title_movie from movies;

select title_movie from movies order by title_movie asc;

select title_movie from movies where director_movie = 'Steven Spielberg';

select title_movie from movies where director_movie is null;

create view v_detail_evaluations as
select ratings.*, reviewers.name_reviewer, movies.title_movie, movies.year_movie, movies.director_movie
from ratings join movies on ratings.id_movie = movies.id_movie join reviewers on reviewers.id_reviewer = ratings.id_reviewer;

select distinct year_movie from v_detail_evaluations where stars_rating in (4, 5) order by year_movie asc;
select distinct name_reviewer from v_detail_evaluations where title_movie = 'Gone with the Wind';

select name_reviewer, title_movie, stars_rating from v_detail_evaluations order by name_reviewer, title_movie, stars_rating asc;

select name_reviewer, title_movie, stars_rating from v_detail_evaluations where name_reviewer = director_movie order by name_reviewer, title_movie, stars_rating asc;

select title_movie from movies right outer join ratings on movies.id_movie = ratings.id_movie where id_reviewer is null;
