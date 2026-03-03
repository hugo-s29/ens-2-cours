CREATE TABLE movies (
    id_movie INT PRIMARY KEY,
    title_movie VARCHAR(255) NOT NULL,
    year_movie INT NOT NULL,
    director_movie VARCHAR(255)
);

CREATE TABLE reviewers (
    id_reviewer INT PRIMARY KEY,
    name_reviewer VARCHAR(255) NOT NULL
);

CREATE TABLE ratings (
    id_reviewer INT,
    id_movie INT,
    stars_rating INT CHECK (stars_rating BETWEEN 1 AND 5),
    date_rating DATE,
    PRIMARY KEY (id_reviewer, id_movie, date_rating),
    FOREIGN KEY (id_reviewer) REFERENCES reviewers(id_reviewer),
    FOREIGN KEY (id_movie) REFERENCES movies(id_movie)
);

insert into movies(id_movie, title_movie, year_movie, director_movie) values
    (101, 'Gone with the Wind', 1939, 'Victor Fleming'),
    (102, 'Star Wars', 1977, 'George Lucas'),
    (103, 'The Sound of Music', 1965, 'Robert Wise'),
    (104, 'E.T.', 1982, 'Steven Spielberg'),
    (105, 'Titanic', 1997, 'James Cameron'),
    (106, 'Snow White', 1937, null),
    (107, 'Avatar', 2009, 'James Cameron'),
    (108, 'Raiders of the Lost Ark', 1981, 'Steven Spielberg')
    (109, 'Star Wars', 1980, 'Georges Lucas'),
;


insert into reviewers(id_reviewer, name_reviewer) values
    (201, 'Sarah Martinez'),
    (202, 'Daniel Lewis'),
    (203, 'Brittany Harris'),
    (204, 'Mike Anderson'),
    (205, 'Chris Jackson'),
    (206, 'Sarah Martinez'),
    (207, 'James Cameron'),
    (208, 'Ashley White')
;

INSERT INTO ratings(id_reviewer, id_movie, stars_rating, date_rating) values
    (201, 101, 2, '2011-01-22'),
    (201, 101, 4, '2015-01-27'),
    (202, 106, 4, '2021-02-04'),
    (203, 101, 2, '2011-02-27'),
    (203, 102, 3, '2011-01-27'),
    (203, 103, 2, '2011-01-20'),
    (203, 104, 2, '2011-03-27'),
    (203, 105, 2, '2011-04-27'),
    (203, 106, 4, '2011-05-27'),
    (203, 107, 5, '2011-06-27')
    (203, 108, 2, '2016-01-30'),
    (203, 108, 4, '2011-01-12'),
    (203, 109, 4, '2013-04-01'),
    (204, 101, 3, '2020-01-09'),
    (205, 103, 3, '2011-01-27'),
    (205, 104, 2, '2011-01-22'),
    (205, 108, 4, '2020-01-27'),
    (206, 106, 5, '2021-01-19'),
    (206, 107, 3, '2015-01-15'),
    (207, 107, 5, '2014-01-20'),
    (208, 104, 3, '2021-01-02'),
;
