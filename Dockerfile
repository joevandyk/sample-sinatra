from ruby:2.5.1
run mkdir /app
workdir /app
copy Gemfile Gemfile.lock ./
run bundle -j4
copy . ./
CMD ./bin/rackup

