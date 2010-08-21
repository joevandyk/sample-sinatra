require 'sinatra'
require 'json'
class SinatraApp < Sinatra::Base

  get '/' do
    content_type 'json'
    {:result => Example.get_something}.to_json
  end

end
